(** Supporting tutorial: one silent round, three infinite-loop behaviors.
    Learn: complete frontiers, return-only Kleisli iteration, and the
    distinction between summary existence and almost-sure termination.
    Reading entries: loop_frontier_exact, loop_classical, loop_probability,
    endless_frontier_zero. Native/frontier: SubEnumQ / observable FreeOmega.
    Probability arithmetic stays in Analysis; no external validation import.
    The genuine model-lfp interpretation is linked in docs/CASE_STUDIES.md. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Prob.Interface Require Import Measure Omega Mixed KleisliIteration.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist RatGeometric.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure.
From PTree.Prob.Backend.EnumQ Require Import Representation Iteration.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure StructuralMeasure Observation.
From PTree.Eq Require Import PTreeKernel UnifiedFrontier.
From PTree.Eq.FreeOmega Require Import Hitting Bind.
From PTree.Interp Require Import FrontierIteration ReturnIteration.
From PTree.Interp.FreeOmega Require Import IterationSummary AbsorbingIteration.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope freeomega_scope.
Import SemanticMeasureNotations SemanticOmegaNotations.
Local Open Scope semantic_measure_scope.
Import HittingNotations.
Local Open Scope hitting_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Module IterationBasics.
Variant eventE : Type → Type := Ask : eventE bool.
Local Notation MN := SubEnumQ.
Local Notation MF := (FreeOmega MN).
Local Notation NI := SubEnumQ_SemanticMeasure.
Local Notation NO := SubEnumQ_SemanticOmega.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation tree := (ptree eventE MN).
Local Notation expect := finite_subdist_expect.

(** Setup: false = geometric retry; true = an additional missing quarter.
    Both retry with probability 1/2. No renormalization is performed. *)
Definition return_mass (partial : bool) : rat := if partial then 1/2 else 1.
Definition round_data partial : list (rat * (unit+bool)) :=
  [(1/2, inl tt); (return_mass partial / 2, inr true)].
Lemma round_nonnegative partial : finite_nonnegative (round_data partial).
Proof.
  intros p x [H|[H|[]]]; inversion H; subst; destruct partial; by vm_compute.
Qed.
Lemma round_bounded partial : finite_expect (λ _, 1) (round_data partial) <= 1.
Proof. destruct partial; by vm_compute. Qed.
Definition kernel (partial : bool) (_ : unit) : MN (unit+bool) :=
  subenumQ_of_list (@round_nonnegative partial) (round_bounded partial).
Definition result_data partial : list (rat * bool) := [(return_mass partial, true)].
Lemma result_nonnegative partial : finite_nonnegative (result_data partial).
Proof. intros p x [H|[]]; inversion H; subst; destruct partial; by vm_compute. Qed.
Lemma result_bounded partial : finite_expect (λ _, 1) (result_data partial) <= 1.
Proof. destruct partial; by vm_compute. Qed.
Definition result (partial : bool) : MN bool :=
  subenumQ_of_list (@result_nonnegative partial) (result_bounded partial).

(** Programs. The ambient signature is inhabited, but these rounds are
    silent. Tau deliberately separates program syntax from its summary. *)
Definition step partial (_ : unit) : tree (unit+bool) :=
  Tau (sample (kernel partial tt)).
Definition loop partial : tree bool := PTree.iter (step partial) tt.
(** Sample a native round outcome, then return its stable head as a measure
    value. [ηω] is measure return; [FHRet] is the head, not another program. *)
Definition round_front partial (_ : unit) :=
  (v ←ω kernel partial tt ;; ηω (FHRet v)) : MF (stable_head eventE MN (unit+bool)).
Definition loop_front partial := complete_iteration_frontier (step partial) (round_front partial) tt.
(** [supω] builds the formal limit expression; [loop_classical] below relates
    it to the complete frontier using the iteration laws. *)
Definition classical_result partial :=
  supω n, mixed_iter_approx (FI := FI) (FO := FO) n (kernel partial) tt.

(** Main frontier calculation: one local certificate, then one library law. *)
Lemma round_complete partial i : step partial i ⇓ₕ round_front partial i.
Proof.
  apply stable_hitting_tau.
  eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure))
    with (Good := λ _, True).
  - apply sem_ae_true.
  - intros v _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.
Theorem loop_frontier_exact partial : loop partial ⇓ₕ loop_front partial.
Proof. apply complete_iteration_hitting. exact (round_complete partial). Qed.
Theorem loop_classical partial :
  loop_front partial ≈ₘ iteration_return_map (classical_result partial).
Proof.
  eapply (iteration_summary_mixed_iter (step := step partial) (NI := NI)); try typeclasses eauto.
  - apply sem_eq_refl.
  - apply sem_eq_refl.
Qed.
Theorem loop_round_is_classical partial n :
  iteration_summary_round (FI := FI) (FO := FO) (step partial) (round_front partial) n tt
    ≈ₘ iteration_return_map (mixed_iter_approx (FI := FI) (FO := FO) (S n) (kernel partial) tt).
Proof.
  exact (iteration_summary_round_mixed_iter (FI := FI) (FO := FO)
    (step partial) (NI := NI) (kernel partial) n tt).
Qed.

(** Analysis: finite expectations, geometric decay, and the resulting
    native observation. No hitting schedule or loop coinduction occurs. *)
Lemma kernel_expect partial i f :
  expect (kernel partial i) f = (1/2)*f (inl tt) + (return_mass partial/2)*f (inr true).
Proof.
  change ((1/2)*f (inl tt) + ((return_mass partial/2)*f (inr true) + 0) =
    (1/2)*f (inl tt) + (return_mass partial/2)*f (inr true)).
  by rewrite addr0.
Qed.
Lemma result_expect partial f : expect (result partial) f = return_mass partial * f true.
Proof. change (return_mass partial * f true + 0 = return_mass partial * f true). by rewrite addr0. Qed.
Definition rows partial n := iteration_observation_round (kernel partial) (λ b, b) n tt.
Local Lemma geometric_update (r x z : rat) :
  r * ((1-x)*z) + (1-r)*z = (1-r*x)*z.
Proof. rewrite mulrA -mulrDl mulrBr mulr1. by rewrite addrC subrKA. Qed.
Local Lemma success_factor partial :
  return_mass partial / 2 = (1 - 1/2) * return_mass partial.
Proof. destruct partial; by vm_compute. Qed.
Lemma rows_expect partial n f :
  expect (rows partial n) f = (1 - (1/2)^+n) * expect (result partial) f.
Proof.
  induction n as [|n IH].
  - change (0 = (1 - (1/2)^+0) * expect (result partial) f). by rewrite expr0 subrr mul0r.
  - change (expect (kernel partial tt >>=ₘ (λ v, match v with
      | inl _ => rows partial n | inr b => ηₘ b end)) f =
      (1 - (1/2)^+(S n)) * expect (result partial) f).
    rewrite finite_subdist_expect_bind kernel_expect finite_subdist_expect_ret IH result_expect exprS.
    rewrite success_factor -[(1 - 1/2) * return_mass partial * f true]mulrA.
    apply geometric_update.
Qed.
Lemma result_indicator_bound partial (P : bool → bool) :
  `|expect (result partial) (λ b, if P b then 1 else 0)| <= 1.
Proof. rewrite result_expect; destruct partial, (P true); by vm_compute. Qed.
Local Lemma decay_difference (x z : rat) : (1-x)*z-z = -(x*z).
Proof. rewrite mulrBl mul1r. apply: (addrI z). by rewrite addrC subrK. Qed.
Lemma rows_limit partial : rows partial ⇑ₘ result partial.
Proof.
  intros P eps Heps.
  have Hhalf0 : (0 : rat) <= 1/2 by vm_compute.
  have Hcontract : (1/2 : rat) <= (1%:R : rat) / 2%:R by vm_compute.
  destruct (rat_contract_vanishes (K := 1%nat) (ltac:(lia)) Hhalf0 Hcontract Heps) as [N HN].
  exists N. intros n Hn.
  change (`|expect (rows partial n) (λ b, if P b then 1 else 0) -
    expect (result partial) (λ b, if P b then 1 else 0)| < eps).
  rewrite rows_expect decay_difference normrN normrM.
  have Hp := exprn_ge0 n Hhalf0.
  rewrite (ger0_norm Hp).
  apply: le_lt_trans (HN n Hn).
  apply: le_trans (ler_wpM2l Hp (result_indicator_bound partial P)) _.
  by rewrite mulr1.
Qed.

(** The observation convenience retains the complete MF frontier. It only
    asks for the selected observation's native limit, not a new semantics. *)
Definition return_value (h : stable_head eventE MN bool) :=
  match h with FHRet b => b | FHVis _ _ _ => false end.
Definition observed_front partial := iteration_frontier (E := eventE) (kernel partial) tt.
Theorem observed_front_exact partial : loop partial ⇓ₕ observed_front partial.
Proof.
  eapply iteration_frontier_summary_hitting; try typeclasses eauto.
  exact (round_complete partial).
Qed.
Theorem two_frontiers_agree partial : loop_front partial ≈ₘ observed_front partial.
Proof. eapply ptree_stable_hitting_unique; [apply loop_frontier_exact|apply observed_front_exact]. Qed.
Theorem loop_observation partial : free_omega_observes return_value (observed_front partial) (result partial).
Proof.
  apply iteration_frontier_observes with (value := λ b, b);
    [reflexivity|apply rows_limit].
Qed.
Theorem loop_returns_only partial :
  free_omega_ae (λ h, ∃ b, h = FHRet b) (observed_front partial).
Proof. apply iteration_frontier_returns. Qed.
Theorem loop_probability partial :
  loop partial ⇓ₕ observed_front partial ∧
  free_omega_observes return_value (observed_front partial) (result partial) ∧
  expect (result partial) (λ _, 1) = return_mass partial.
Proof. split; [apply observed_front_exact|]. split; [apply loop_observation|]. by rewrite result_expect mulr1. Qed.
Corollary geometric_returns_mass_one : expect (result false) (λ _, 1) = 1.
Proof. exact (proj2 (proj2 (loop_probability false))). Qed.
Corollary partial_returns_mass_half : expect (result true) (λ _, 1) = 1/2.
Proof. exact (proj2 (proj2 (loop_probability true))). Qed.
Corollary geometric_ast : loop false ⇓ₕ¹ observed_front false.
Proof.
  split; [apply observed_front_exact|].
  apply free_omega_observable_total_intro.
  exists bool, return_value, (result false). split; [apply loop_observation|].
  exact geometric_returns_mass_one.
Qed.

(** Third version: every round finishes, but only with retry. *)
Definition endless_step (_ : unit) : tree (unit+bool) := Ret (inl tt).
Definition endless : tree bool := PTree.iter endless_step tt.
Definition endless_front (_ : unit) : MF (stable_head eventE MN (unit+bool)) := ηω (FHRet (inl tt)).
Lemma endless_round_zero n :
  iteration_summary_round (FI := FI) (FO := FO) endless_step endless_front n tt = ⊥ω.
Proof. induction n; [reflexivity|exact IHn]. Qed.
Theorem endless_frontier_zero : endless ⇓ₕ ⊥ω.
Proof.
  eapply (iteration_summary_hitting (FI := FI) (FO := FO) (front := endless_front)); try typeclasses eauto.
  - intro i. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
  - eapply sem_lub_chain_proper with (chain := λ _, ⊥ω).
    + intro n. rewrite endless_round_zero. apply sem_eq_refl.
    + apply sem_lub_constant.
Qed.
Corollary endless_observation_zero :
  free_omega_observes return_value (⊥ω : MF (stable_head eventE MN bool))
    (⊥ₘ : MN bool).
Proof. constructor. Qed.
End IterationBasics.
