(** Case role: paper case study.
    Reading entry: Adaptive.controller_program_rewrite.
    Native/frontier: SubEnumQ / observable FreeOmega; all primitive draws total.
    Internal effects are interpreted into State, then State is threaded out.
    State is NOT reset between attempts, factory iterations or requests.
    See docs/CASE_STUDIES.md#factory-controllers for the proved contract and boundaries. *)
(** Learn: handler algebra, complete-round analysis, then relational protocol refinement.
    Reusable endpoints: Adaptive.loop_hits, raw_loop_fair, adaptive_factory_direct, controller_refinement.
    Boundary: successful state and bit remain correlated; no new execution claim.
    User navigation: docs/CASE_STUDIES.md. *)
(** Reading order: 1. Setup; 2. Programs; 3. Analysis and component equations;
    4. Full-program calculation; 5. Reusable consequences.
    For the algebraic story, read [adaptive_factory_direct] and then
    [controller_program_rewrite]. The finite/limit analysis stays in §3. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.
From Coq Require Import List Morphisms.
From Coq.Program Require Import Equality.
From ITree.Basics Require Import Monad.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Eq.FreeOmega Require Import Relation Hitting.
From PTree.Eq Require Import PTreeKernel UnifiedFrontier Shallow.
From PTree.Prob.Interface Require Import Measure AE Omega Mixed.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Observation Approximation StructuralMeasure
  SupportLift Quotient Measure RelationalLimit.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.EnumQ Require Import Representation Bind Iteration.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist RatGeometric FiniteRecordExtensionality.
From PTree.Interp Require Import State StateIter.
From PTree.Interp Require Import Iteration IterationUniform.
From PTree.Interp.Algebra Require Import State Computation.
From PTree.Interp.FreeOmega Require Import Base Rewriting Unrestricted IterationSummary.
From PTree.Examples.BernoulliFactory Require Import
  VonNeumannUnbounded RationalBernoulli BernoulliFactory BoundedFactory.
Import EnumQ GRing.Theory Num.Theory Order.Theory FreeOmegaRewriting.
Local Open Scope ring_scope.
Import MonadNotation SemanticMeasureNotations SemanticOmegaNotations.
Local Open Scope monad_scope.
Local Open Scope freeomega_scope.
Local Open Scope semantic_measure_scope.
Import HittingNotations.
Local Open Scope hitting_scope.

Module Adaptive.
Import BoundedFactory.
Local Notation expect f mu := (finite_subdist_expect mu f).

(** 1. Setup: bounded sources, persistent state and the event signatures.
    [≈ₚ] uses the registered observable FreeOmega interpretation of SubEnumQ. *)

(** Source identity is a Boolean, not the outcome of either sample. *)
Definition low_weight (src : bool) : rat := if src then 1/4 else 1/3.
Definition high_weight src : rat := 1 - low_weight src.
Lemma low_nonnegative src : 0 <= low_weight src.
Proof. destruct src; by vm_compute. Qed.
Lemma high_nonnegative src : 0 <= high_weight src.
Proof. destruct src; by vm_compute. Qed.
Lemma source_bounded src :
  enumQ_subprob (param_biased_coin (low_nonnegative src) (high_nonnegative src)).
Proof. destruct src; by vm_compute. Qed.
Definition source_coin src : SubEnumQ bool := enumQ_as_subprob (source_bounded src).
Lemma source_coin_raw src : subenumQ_raw (source_coin src) =
  param_biased_coin (low_nonnegative src) (high_nonnegative src).
Proof. reflexivity. Qed.
Lemma source_coin_total src : sem_total (source_coin src).
Proof. destruct src; by vm_compute. Qed.

(** Health feeds back into sampling; retries is private bookkeeping only.
    Both persist across attempts, factory rounds and public requests. The
    specification returns just a bit, related by [output_related] below. *)
Record machine_state := MachineState { health : bool; retries : nat }.
Definition initial_state := MachineState false 0.
Definition after_sensor s report :=
  MachineState (xorb (health s) report) (retries s).
Definition retry_update s := MachineState (health s) (S (retries s)).

Variant publicE : Type → Type :=
| Request : publicE unit
| Emit : bool → publicE unit.
Variant internalE : Type → Type :=
| ChooseSource : internalE bool
| CheckSensor : bool → internalE bool
| Retry : internalE unit.
Definition implE := stateE machine_state +' (internalE +' publicE).
Definition targetE := stateE machine_state +' publicE.
Local Notation tree := (ptree implE SubEnumQ).

(** 2. Programs: private interpretation, adaptive sampler, public controller. *)

(** Program sequencing uses [sample] / [trigger] and [<- ;;]. Later,
    [>>=ₘ] composes native distributions, while [←ω ;;] builds a FreeOmega
    frontier. These are distinct layers, not competing program notations. *)

Definition internal {X} (e : internalE X) : tree X :=
  PTree.trigger (inr1 (inl1 e)).
Definition public {X} (e : publicE X) : tree X :=
  PTree.trigger (inr1 (inr1 e)).
Definition update (f : machine_state → machine_state) : tree unit :=
  s <- PTree.trigger (inl1 (Get machine_state));;
  PTree.trigger (inl1 (Put machine_state (f s))).

Definition internal_handler X (e : implE X) : ptree targetE SubEnumQ X :=
  match e with
  | inl1 se => PTree.trigger (inl1 se)
  | inr1 (inr1 pe) => PTree.trigger (inr1 pe)
  | inr1 (inl1 ie) =>
    match ie with
    | ChooseSource =>
        s <- PTree.trigger (inl1 (Get machine_state));;
        Ret (health s)
    | CheckSensor a => Ret a
    | Retry =>
        s <- PTree.trigger (inl1 (Get machine_state));;
        PTree.trigger (inl1 (Put machine_state (retry_update s)))
    end
  end.
Definition lower {A} (t : tree A) s := run_state (PTree.interp internal_handler t) s.

(** [src] is bound before either sample; changing health between them cannot
    change this attempt's second sampling distribution. *)
Definition vn_attempt (_ : unit) : tree (unit + bool) :=
  src <- internal ChooseSource;;
  a <- sample (source_coin src);;
  report <- internal (CheckSensor a);;
  update (λ s, after_sensor s report);;
  b <- sample (source_coin src);;
  if a == b then internal Retry;; Ret (inl tt)
  else Ret (inr a).
Definition adaptive_vn : tree bool := PTree.iter vn_attempt tt.

Definition factory_step (x : rat) : tree (rat + bool) :=
  b <- adaptive_vn;;
  Ret (binary_round_result x b).
Definition eventful_factory q : tree bool := PTree.iter factory_step q.
Definition serve_request q : tree unit :=
  public Request;;
  b <- eventful_factory q;;
  public (Emit b).
Definition controller q : tree Empty_set :=
  PTree.iter (λ _ : unit, serve_request q;; Ret (inl tt)) tt.

Definition serve_spec q (q0 : 0 <= q) (q1 : q <= 1) : ptree publicE SubEnumQ unit :=
  PTree.trigger Request;;
  b <- sample (bernoulli q0 q1);;
  PTree.trigger (Emit b).
Definition controller_spec q (q0 : 0 <= q) (q1 : q <= 1) :
    ptree publicE SubEnumQ Empty_set :=
  PTree.iter (λ _ : unit, serve_spec q0 q1;; Ret (inl tt)) tt.

(** 3. Analysis and local equations.

    3.1. Normalize one attempt using handler/State/bind equations.
    These equations thread state; none resets or abstracts it. *)
Lemma lower_ret {A} (a : A) s : lower (Ret a) s ≈ₚ Ret (s,a).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Lemma lower_bind {A B} (t : tree A) (k : A → tree B) s :
  lower (x <- t;; k x) s ≈ₚ
  (sa <- lower t s;; lower (k (snd sa)) (fst sa)).
Proof.
  unfold lower. setoid_rewrite peutt_interp_bind.
  apply peutt_of_pstruct.
  exact (@run_state_bind machine_state publicE SubEnumQ A B
    (PTree.interp internal_handler t) (λ x, PTree.interp internal_handler (k x)) s).
Qed.

Lemma lower_prob {A X} (mu : SubEnumQ X) (k : X → tree A) s :
  lower (Prob mu k) s ≈ₚ Prob mu (λ x, lower (k x) s).
Proof.
  unfold lower. setoid_rewrite peutt_interp_prob.
  apply run_state_prob.
Qed.

(** One equation for all private events. It exposes deterministic state
    updates; it does not erase state or postulate a handler law. *)
Lemma lower_internal {X} (e : internalE X) s :
  lower (internal e) s ≈ₚ Ret
    (match e in internalE Y return machine_state * Y with
     | ChooseSource => (s, health s)
     | CheckSensor a => (s, a)
     | Retry => (retry_update s, tt)
     end).
Proof.
  destruct e; repeat (eapply peutt_tau_step; [cbn; reflexivity|]);
    apply peutt_observe_eq; reflexivity.
Qed.

Lemma lower_update f s : lower (update f) s ≈ₚ Ret (f s,tt).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  apply peutt_observe_eq. reflexivity.
Qed.

Definition lowered_step {I A} (step : I → tree (I+A)) (si : machine_state * I) :=
  sa <- lower (step (snd si)) (fst si);;
  Ret (state_iter_result sa).
Lemma lower_iter {I A} (step : I → tree (I+A)) i s :
  lower (PTree.iter step i) s ≈ₚ PTree.iter (lowered_step step) (s,i).
Proof.
  unfold lower. setoid_rewrite peutt_interp_iter.
  apply peutt_of_pstruct.
  exact (@run_state_iter machine_state I A publicE SubEnumQ
    (λ i, PTree.interp internal_handler (step i)) i s).
Qed.
Lemma lower_public {X} (e : publicE X) s :
  lower (public e) s ≈ₚ Vis e (λ x, Ret (s,x)).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  transitivity (Vis e (λ x, run_state
    (PTree.bind (Ret x) (λ y, PTree.interp internal_handler (Ret y))) s)).
  - apply peutt_observe_eq. reflexivity.
  - apply peutt_vis. intro x. apply peutt_observe_eq. reflexivity.
Qed.
Definition state_attempt_result s a b : machine_state * (unit + bool) :=
  if a == b then (retry_update (after_sensor s a), inl tt)
  else (after_sensor s a, inr a).

Theorem lower_attempt s :
  lower (vn_attempt tt) s ≈ₚ
  Prob (source_coin (health s)) (λ a,
    Prob (source_coin (health s)) (λ b, Ret (state_attempt_result s a b))).
Proof.
  unfold vn_attempt, sample.
  setoid_rewrite lower_bind. setoid_rewrite lower_internal.
  setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite lower_bind.
  setoid_rewrite lower_prob.
  setoid_rewrite peutt_bind_prob.
  setoid_rewrite lower_ret. setoid_rewrite peutt_bind_ret_l.
  apply peutt_prob_Proper. intros a.
  setoid_rewrite lower_bind. setoid_rewrite lower_internal.
  setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite lower_bind.
  setoid_rewrite lower_update. setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite lower_bind. setoid_rewrite lower_prob.
  setoid_rewrite peutt_bind_prob.
  setoid_rewrite lower_ret. setoid_rewrite peutt_bind_ret_l.
  apply peutt_prob_Proper. intro b.
  cbn [fst snd]. unfold state_attempt_result. destruct (a == b).
  - setoid_rewrite lower_bind. setoid_rewrite lower_internal.
    setoid_rewrite peutt_bind_ret_l. setoid_rewrite lower_ret. reflexivity.
  - setoid_rewrite lower_ret. reflexivity.
Qed.

(** Exact stateful kernel of one attempt. Successful states may depend on
    the returned bit; both failed states remain available to the retry. *)
Definition decode_attempt (sa : machine_state * (unit + bool)) :
    machine_state + (machine_state * bool) :=
  match snd sa with inl _ => inl (fst sa) | inr b => inr (fst sa,b) end.
Definition attempt_result s a b := decode_attempt (state_attempt_result s a b).
Definition attempt_kernel s : SubEnumQ (machine_state + (machine_state * bool)) :=
  source_coin (health s) >>=ₘ λ a,
  source_coin (health s) >>=ₘ λ b,
  ηₘ (attempt_result s a b).

Theorem lower_attempt_kernel s :
  (sa <- lower (vn_attempt tt) s;; Ret (decode_attempt sa)) ≈ₚ
  sample (attempt_kernel s).
Proof.
  setoid_rewrite lower_attempt.
  setoid_rewrite peutt_bind_prob.
  setoid_rewrite peutt_bind_prob.
  setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite (peutt_sample_map (MF := FreeOmega SubEnumQ) (source_coin (health s))).
  setoid_rewrite peutt_prob_flatten.
  reflexivity.
Qed.

(** Infinite-loop normalization is an algebraic consumer of the attempt
    calculation. It retains all state; fairness is proved separately below. *)
Definition normalized_step (si : machine_state * unit) :
    ptree publicE SubEnumQ ((machine_state * unit) + (machine_state * bool)) :=
  Prob (source_coin (health (fst si))) (λ a,
  Prob (source_coin (health (fst si))) (λ b,
    Ret (state_iter_result (state_attempt_result (fst si) a b)))).

Theorem lower_adaptive_normalized s :
  lower adaptive_vn s ≈ₚ PTree.iter normalized_step (s,tt).
Proof.
  unfold adaptive_vn. setoid_rewrite lower_iter.
  have Hstep : pointwise_relation _ (λ t u, t ≈ₚ u)
      (lowered_step vn_attempt) normalized_step.
  { intros [s' []]. unfold lowered_step, normalized_step; cbn [fst snd].
    setoid_rewrite lower_attempt.
    setoid_rewrite peutt_bind_prob.
    setoid_rewrite peutt_bind_prob.
    setoid_rewrite peutt_bind_ret_l. reflexivity. }
  setoid_rewrite Hstep. reflexivity.
Qed.

(** 3.2. Finite probability analysis. Retain the full state/bit experiment,
    prove symmetry and a uniform geometric tail; do not assume independence. *)

Lemma source_expect src (f : bool → rat) :
  expect f (source_coin src) =
    low_weight src * f false + high_weight src * f true.
Proof.
  change (enumQ_expect f (param_biased_coin (low_nonnegative src) (high_nonnegative src)) =
    low_weight src * f false + high_weight src * f true).
  rewrite /param_biased_coin !enumQ_expect_cons enumQ_expect_nil addr0.
  reflexivity.
Qed.

Lemma attempt_expect s (f : machine_state + (machine_state * bool) → rat) :
  expect f (attempt_kernel s) =
    low_weight (health s) *
      (low_weight (health s) * f (inl (retry_update (after_sensor s false))) +
       high_weight (health s) * f (inr (after_sensor s false, false))) +
    high_weight (health s) *
      (low_weight (health s) * f (inr (after_sensor s true, true)) +
       high_weight (health s) * f (inl (retry_update (after_sensor s true)))).
Proof.
  cbn [attempt_kernel sem_bind sem_ret SubEnumQ_SemanticMeasure].
  rewrite finite_subdist_expect_bind source_expect.
  rewrite !finite_subdist_expect_bind !source_expect.
  rewrite !finite_subdist_expect_ret. reflexivity.
Qed.

(** A complete finite experiment: inl means all n attempts failed, inr means
    success with its actual state. This is not internal-node fuel. *)
Fixpoint attempts (n : nat) s : SubEnumQ (machine_state + (machine_state * bool)) :=
  match n with
  | O => ηₘ (inl s)
  | S k => attempt_kernel s >>=ₘ λ result,
      match result with inl s' => attempts k s' | inr sb => ηₘ (inr sb) end
  end.
Definition pending (x : machine_state + (machine_state * bool)) : rat :=
  match x with inl _ => 1 | inr _ => 0 end.
Definition returns (b : bool) (x : machine_state + (machine_state * bool)) : rat :=
  match x with inl _ => 0 | inr sb => if snd sb == b then 1 else 0 end.

Lemma attempts_expect_S n s f :
  expect f (attempts (S n) s) =
    low_weight (health s) *
      (low_weight (health s) * expect f (attempts n (retry_update (after_sensor s false))) +
       high_weight (health s) * f (inr (after_sensor s false, false))) +
    high_weight (health s) *
      (low_weight (health s) * f (inr (after_sensor s true, true)) +
       high_weight (health s) * expect f (attempts n (retry_update (after_sensor s true)))).
Proof.
  cbn [attempts sem_bind sem_ret SubEnumQ_SemanticMeasure].
  rewrite finite_subdist_expect_bind attempt_expect /= !finite_subdist_expect_ret. reflexivity.
Qed.

Lemma retry_bound src : low_weight src ^+ 2 + high_weight src ^+ 2 <= (5/8 : rat).
Proof. destruct src; by vm_compute. Qed.

Lemma source_normalized src : low_weight src + high_weight src = 1.
Proof. rewrite /high_weight addrC subrK. reflexivity. Qed.

Theorem attempts_total n s : expect (λ _, 1) (attempts n s) = 1.
Proof.
  elim: n s => [|n IH] s; first reflexivity.
  rewrite attempts_expect_S !IH !mulr1 source_normalized !mulr1 source_normalized.
  reflexivity.
Qed.

Theorem attempts_symmetric n s :
  expect (returns false) (attempts n s) =
  expect (returns true) (attempts n s).
Proof.
  elim: n s => [|n IH] s; first reflexivity.
  rewrite !attempts_expect_S /returns /= !mulr0 !mulr1 !addr0 !add0r.
  rewrite !mulrDr !mulrA -!addrA.
  rewrite -/(returns false) -/(returns true) !IH.
  by rewrite /high_weight !mulrDl !mul1r !mulNr !mulrN !mulr1 -!addrA.
Qed.

Theorem adaptive_pending_bound n s :
  expect pending (attempts n s) <= (5/8 : rat) ^+ n.
Proof.
  elim: n s => [|n IH] s.
  - change ((1 : rat) <= 1). exact: lexx.
  - rewrite attempts_expect_S /pending !mulr0 addr0 add0r !mulrA -!expr2
      (exprS (5/8 : rat) n).
    have Hl := ler_wpM2l (exprn_ge0 2 (low_nonnegative (health s)))
      (IH (retry_update (after_sensor s false))).
    have Hr := ler_wpM2l (exprn_ge0 2 (high_nonnegative (health s)))
      (IH (retry_update (after_sensor s true))).
    apply: le_trans (lerD Hl Hr) _.
    rewrite -mulrDl.
    have Hbase : (0 : rat) <= 5/8 by vm_compute.
    exact: (ler_wpM2r (exprn_ge0 n Hbase) (retry_bound (health s))).
Qed.

Theorem adaptive_pending_vanishes s eps : 0 < eps →
  ∃ N, ∀ n, (N <= n)%coq_nat → expect pending (attempts n s) < eps.
Proof.
  intro Heps.
  have Hpos : (0 < 2)%coq_nat by repeat constructor.
  have Hnonneg : (0 : rat) <= 5/8 by vm_compute.
  have Hcontract : (5/8 : rat) <= 2%:R / 3%:R by vm_compute.
  destruct (rat_contract_vanishes Hpos Hnonneg Hcontract Heps) as [N HN].
  exists N. intros n Hn. exact: le_lt_trans (adaptive_pending_bound n s) (HN n Hn).
Qed.

Theorem attempts_partition n s :
  expect (returns false) (attempts n s) +
  expect (returns true) (attempts n s) +
  expect pending (attempts n s) = 1.
Proof.
  have H : expect (λ x, returns false x + returns true x + pending x)
      (attempts n s) = 1.
  { transitivity (expect (λ _, 1) (attempts n s)).
    - apply finite_expect_ext. intros [s'|[s' b]]; first reflexivity.
      destruct b; by vm_compute.
    - apply attempts_total. }
  move: H. rewrite /finite_subdist_expect /finite_enum_expect !finite_expect_add.
  exact (λ H, H).
Qed.

Theorem attempts_return_probability n s b :
  expect (returns b) (attempts n s) =
    (1 - expect pending (attempts n s)) / 2.
Proof.
  have H := attempts_partition n s.
  have Hsym := attempts_symmetric n s.
  destruct b.
  - rewrite Hsym in H.
    apply (mulIf (x := (2 : rat))); first by vm_compute.
    rewrite divrK; last by vm_compute.
    apply: (addIr (expect pending (attempts n s))).
    rewrite subrK mulr_natr mulr2n. exact H.
  - rewrite -Hsym in H.
    apply (mulIf (x := (2 : rat))); first by vm_compute.
    rewrite divrK; last by vm_compute.
    apply: (addIr (expect pending (attempts n s))).
    rewrite subrK mulr_natr mulr2n. exact H.
Qed.

Theorem adaptive_return_limit s b eps : 0 < eps →
  ∃ N, ∀ n, (N <= n)%coq_nat →
    `|expect (returns b) (attempts n s) - (1/2 : rat)| < eps.
Proof.
  intro Heps. destruct (adaptive_pending_vanishes s Heps) as [N HN].
  exists N. intros n Hn.
  have Htail : 0 <= expect pending (attempts n s).
  { apply finite_expect_nonnegative; first exact (enumQ_nonnegative (subenumQ_raw (attempts n s))).
    intros [s'|sb]; by vm_compute. }
  rewrite attempts_return_probability vn_difference normrN normrM (ger0_norm Htail).
  have Hhalf : `|(1/2 : rat)| <= 1 by vm_compute.
  have Hle := ler_wpM2l Htail Hhalf.
  rewrite mulr1 in Hle. exact: le_lt_trans Hle (HN n Hn).
Qed.

(** Boundary checks: adaptation is real, and successful state is correlated
    with the returned bit. Neither fact is silently erased by the analysis. *)
Example retry_can_switch_source :
  health initial_state = false ∧
  health (retry_update (after_sensor initial_state true)) = true.
Proof. split; reflexivity. Qed.
Example failed_branches_persist s :
  attempt_result s false false = inl (MachineState (health s) (S (retries s))) ∧
  attempt_result s true true = inl (MachineState (negb (health s)) (S (retries s))).
Proof. destruct s as [[] n]; split; reflexivity. Qed.
Example successful_states_distinct :
  after_sensor initial_state false ≠ after_sensor initial_state true.
Proof. discriminate. Qed.
Example different_retry_rates :
  low_weight false ^+ 2 + high_weight false ^+ 2 <
  low_weight true ^+ 2 + high_weight true ^+ 2.
Proof. by vm_compute. Qed.

(** A true/true failure flips health, so two attempts do NOT have the
    fixed-source tail [(5/9)^2]. This checks the actual stateful experiment. *)
Example two_attempts_are_adaptive :
  expect pending (attempts 2 initial_state) = (55/162 : rat) ∧
  expect pending (attempts 2 initial_state) ≠ (5/9 : rat) ^+ 2.
Proof. split; by vm_compute. Qed.

(** 3.3. Connect complete attempts to actual stable hitting. The
    observer rejects visible heads; None is never part of the limit law. *)
Definition bit_observer {A} (value : A → bool)
    (h : stable_head publicE SubEnumQ A) : option bool :=
  match h with FHRet a => Some (value a) | FHVis _ _ _ => None end.
Definition raw_loop s := PTree.iter normalized_step (s,tt).
(** One-round kernel compilation uses finite hitting laws. The library handles all
    iteration scheduling, even though publicE is inhabited. *)
Definition loop_kernel (si : machine_state * unit) :=
  source_coin (health (fst si)) >>=ₘ λ a,
  source_coin (health (fst si)) >>=ₘ λ b,
  ηₘ (state_iter_result (state_attempt_result (fst si) a b)).
Definition loop_heads s := iteration_frontier (E := publicE) loop_kernel (s,tt).
Lemma loop_hits s : raw_loop s ⇓ₕ loop_heads s.
Proof.
  eapply iteration_frontier_summary_hitting; try typeclasses eauto.
  intros [s' []]. unfold normalized_step, loop_kernel; cbn [fst].
  eapply stable_hitting_native_sample; try typeclasses eauto. intro a.
  eapply stable_hitting_native_sample; try typeclasses eauto. intro b.
  apply stable_hitting_native_ret.
Qed.

Fixpoint output_row n s : SubEnumQ (option bool) :=
  match n with
  | O => ⊥ₘ
  | S k => source_coin (health s) >>=ₘ λ a,
      source_coin (health s) >>=ₘ λ b,
      if a == b then output_row k (retry_update (after_sensor s a))
      else ηₘ (Some a)
  end.
(** The only bridge calculation left in the case is finite native
    associativity: the compiled round has the same bit observation. *)
Lemma loop_round_observation n s :
  iteration_observation_round loop_kernel (λ sb, Some (snd sb)) n (s,tt) =
  output_row n s.
Proof.
  revert s. induction n as [|n IH]; intro s; [reflexivity|].
  cbn [iteration_observation_round output_row].
  unfold loop_kernel.
  change (((source_coin (health s) >>=ₘ λ a,
      source_coin (health s) >>=ₘ λ b,
      ηₘ (state_iter_result (state_attempt_result s a b))) >>=ₘ
    λ next, match next with
      | inl si => iteration_observation_round loop_kernel (λ sb, Some (snd sb)) n si
      | inr sb => ηₘ (Some (snd sb)) end) =
    (source_coin (health s) >>=ₘ λ a,
     source_coin (health s) >>=ₘ λ b,
     if a == b then output_row n (retry_update (after_sensor s a))
     else ηₘ (Some a))).
  cbn [sem_bind sem_ret SubEnumQ_SemanticMeasure].
  unfold subenumQ_bind, subenumQ_ret.
  rewrite finite_subdist_bind_assoc_eq.
  apply finite_subdist_bind_ext_eq=> a. rewrite finite_subdist_bind_assoc_eq.
  apply finite_subdist_bind_ext_eq=> b. rewrite finite_subdist_bind_ret_eq.
  destruct a,b; cbn [state_iter_result state_attempt_result attempt_result decode_attempt];
    try reflexivity; apply IH.
Qed.

Lemma output_row_expect n s f : expect f (output_row n s) =
  expect (λ z, match z with inl _ => 0 | inr sb => f (Some (snd sb)) end)
    (attempts n s).
Proof.
  revert s. induction n as [|n IH]; intro s.
  - reflexivity.
  - rewrite attempts_expect_S.
    cbn [output_row sem_bind sem_ret SubEnumQ_SemanticMeasure].
    rewrite finite_subdist_expect_bind source_expect !finite_subdist_expect_bind !source_expect.
    rewrite ?finite_subdist_expect_ret !IH. reflexivity.
Qed.
Definition fair_options : SubEnumQ (option bool) :=
  fair_coin >>=ₘ λ b, ηₘ (Some b).
Lemma fair_options_expect f : expect f fair_options =
  (1/2 : rat) * (f (Some false) + f (Some true)).
Proof.
  change ((1/2) * f (Some false) + ((1/2) * f (Some true) + 0) =
    (1/2) * (f (Some false) + f (Some true))).
  by rewrite addr0 mulrDr.
Qed.
Lemma output_row_factor n s f : expect f (output_row n s) =
  (1 - expect pending (attempts n s)) * expect f fair_options.
Proof.
  rewrite output_row_expect.
  transitivity (expect (λ z,
    f (Some false) * returns false z + f (Some true) * returns true z) (attempts n s)).
  - apply finite_expect_ext. intros [s'|[s' b]]; [|destruct b];
      cbn [returns snd]; rewrite ?mulr0 ?mulr1 ?addr0 ?add0r; reflexivity.
  - unfold finite_subdist_expect, finite_enum_expect.
    erewrite finite_expect_add. erewrite finite_expect_scale. erewrite finite_expect_scale.
    change (f (Some false) * expect (returns false) (attempts n s) +
      f (Some true) * expect (returns true) (attempts n s) =
      (1 - expect pending (attempts n s)) * expect f fair_options).
    rewrite !attempts_return_probability fair_options_expect.
    by rewrite -mulrDl mulrC -mulrA.
Qed.
Lemma output_row_converges s :
  (λ n, output_row n s) ⇑ₘ fair_options.
Proof.
  intros P eps Heps. destruct (adaptive_pending_vanishes s Heps) as [N HN].
  exists N. intros n Hn.
  change (`|expect (λ x, if P x then 1 else 0) (output_row n s) -
    expect (λ x, if P x then 1 else 0) fair_options| < eps).
  rewrite output_row_factor vn_difference normrN normrM.
  have Htail : 0 <= expect pending (attempts n s).
  { apply finite_expect_nonnegative; first exact (enumQ_nonnegative (subenumQ_raw (attempts n s))).
    intros [s'|sb]; by vm_compute. }
  rewrite (ger0_norm Htail).
  have Hbound : `|expect (λ x, if P x then 1 else 0) fair_options| <= 1.
  { rewrite fair_options_expect. destruct (P (Some false)), (P (Some true)); by vm_compute. }
  have Hle := ler_wpM2l Htail Hbound. rewrite mulr1 in Hle.
  apply: le_lt_trans Hle _. exact (HN n Hn).
Qed.
Lemma loop_heads_observes s :
  free_omega_observes (bit_observer (@snd machine_state bool)) (loop_heads s) fair_options.
Proof.
  apply iteration_frontier_observes with (value := λ sb, Some (snd sb));
    [reflexivity|].
  intros P eps Heps. destruct (output_row_converges s P Heps) as [N HN].
  exists N. intros n Hn. rewrite loop_round_observation. exact (HN n Hn).
Qed.

Lemma source_ae_inv src P : sem_ae (source_coin src) P → ∀ b, P b.
Proof.
  intros H b. destruct b.
  - apply H with (p := high_weight src).
    + cbn. auto.
    + destruct src; vm_compute; discriminate.
  - apply H with (p := low_weight src).
    + cbn. auto.
    + destruct src; vm_compute; discriminate.
Qed.
Definition fair_tree : ptree publicE SubEnumQ bool := sample fair_coin.
Definition fair_heads : FreeOmega SubEnumQ (stable_head publicE SubEnumQ bool) :=
  b ←ω fair_coin ;; ηω (FHRet b).
Lemma loop_heads_success s P : free_omega_ae P (loop_heads s) →
  ∀ b, P (FHRet (after_sensor s b,b)).
Proof.
  intro HP. unfold loop_heads, iteration_frontier in HP. dependent destruction HP.
  specialize (H 1%nat).
  pose proof (free_omega_ae_sample_inv H) as Hfirst.
  unfold loop_kernel in Hfirst.
  apply (proj1 (sem_ae_bind_iff _ _ _)) in Hfirst.
  pose proof (source_ae_inv Hfirst) as Ha.
  intro b. specialize (Ha b).
  apply (proj1 (sem_ae_bind_iff _ _ _)) in Ha.
  pose proof (source_ae_inv Ha (negb b)) as Hb.
  apply (proj1 (sem_ae_ret_iff _ _)) in Hb.
  destruct b; cbn in Hb; dependent destruction Hb; assumption.
Qed.
Definition output_related (sb : machine_state * bool) (b : bool) := snd sb = b.
Lemma loop_heads_fair_support s sim :
  free_omega_support_lift (stable_head_rel output_related sim) (loop_heads s) fair_heads.
Proof.
  split.
  - intros P HP. eapply FOAESample with (Good := λ _, True); [apply sem_ae_true|].
    intros b _. constructor. exists (FHRet (after_sensor s b,b)). split.
    + constructor. reflexivity.
    + exact (loop_heads_success HP b).
  - intros Q HQ.
    have HQb : ∀ b, free_omega_ae Q (ηω (FHRet b)).
    { intro b. apply (free_omega_ae_sample_inv HQ) with (p := one_div_two).
      - destruct b; cbn; auto.
      - vm_compute; discriminate. }
    eapply free_omega_ae_mono; [|apply iteration_frontier_returns].
    intros h [sb ->]. exists (FHRet (snd sb)). split; [constructor; reflexivity|].
    specialize (HQb (snd sb)). inversion HQb; subst; assumption.
Qed.
Lemma loop_heads_fair_lift s sim :
  free_omega_qlift (stable_head_rel output_related sim) (loop_heads s) fair_heads.
Proof.
  eapply FOQLObserve with
    (obsA := bit_observer (@snd machine_state bool))
    (obsB := bit_observer (λ b, b))
    (outA := fair_options) (outB := fair_options)
    (S := λ x y, exists b, x = Some b ∧ y = Some b).
  - exact (loop_heads_observes s).
  - constructor. intro b. constructor.
  - eapply sem_lift_bind with (R := eq).
    + apply sem_lift_refl. intro b. reflexivity.
    + intros b c ->. apply sem_lift_ret. exists c. auto.
  - intros h1 h2 [b [H1 H2]]. destruct h1 as [sb|X e k], h2 as [c|Y f l];
      cbn [bit_observer] in H1,H2; try discriminate.
    constructor. unfold output_related. congruence.
  - exact (loop_heads_fair_support s sim).
Qed.
Theorem raw_loop_fair s : raw_loop s ≈ₚ[output_related] fair_tree.
Proof.
  eapply peutt_of_hitting_lift.
  - exact (loop_hits s).
  - unfold fair_tree, fair_heads.
    eapply (ptree_stable_hitting_prob (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)) with (Good := λ _, True).
    + apply sem_ae_true.
    + intros b _. apply ptree_stable_hitting_ret.
  - exact (loop_heads_fair_lift s _).
Qed.

Theorem adaptive_vn_fair s : lower adaptive_vn s ≈ₚ[output_related] fair_tree.
Proof.
  setoid_rewrite lower_adaptive_normalized. apply raw_loop_fair.
Qed.
Theorem raw_loop_ast s : raw_loop s ⇓ₕ¹ loop_heads s.
Proof.
  split; [apply loop_hits|]. apply free_omega_observable_total_intro.
  exists (option bool), (bit_observer (@snd machine_state bool)), fair_options.
  split; [apply loop_heads_observes|].
  change (expect (λ _, 1) fair_options = 1).
  rewrite fair_options_expect. by vm_compute.
Qed.

(** 3.4. Component calculation. Consume the two unbounded analyses:
    the adaptive VN result above and the existing binary-factory law below.
    From here on, no finite list or rational-limit calculation is repeated. *)
(** The factory invariant keeps the rational residual target, but permits
    any machine state. One fair bit is enough; state/bit independence is not. *)
Definition factory_states (si : machine_state * rat) q := snd si = q.
Definition embed_closed {A} (t : ptree factoryE SubEnumQ A) : ptree publicE SubEnumQ A :=
  PTree.interp (λ X (e : factoryE X), match e with end) t.
Lemma fair_factory_direct q (q0 : 0 <= q) (q1 : q <= 1) :
  factory_with_sampler fair_tree q ≈ₚ
    sample (bernoulli q0 q1).
Proof.
  have H : embed_closed (factory_with_sampler (sample fair_coin) q) ≈ₚ
      embed_closed (sample (bernoulli q0 q1)).
  { apply peutt_interp. exact (BoundedFactory.fair_factory_direct q0 q1). }
  unfold embed_closed, factory_with_sampler, factory_sampler_step, sample in H.
  setoid_rewrite peutt_interp_iter in H.
  setoid_rewrite peutt_interp_bind in H.
  setoid_rewrite peutt_interp_prob in H.
  setoid_rewrite peutt_interp_ret in H.
  exact H.
Qed.

Theorem adaptive_factory_direct s q (q0 : 0 <= q) (q1 : q <= 1) :
  lower (eventful_factory q) s ≈ₚ[output_related]
    sample (bernoulli q0 q1).
Proof.
  (* Stateful iteration -> fair-bit iteration -> direct Bernoulli. *)
  setoid_rewrite <- (fair_factory_direct q0 q1).
  unfold eventful_factory, factory_with_sampler. setoid_rewrite lower_iter.
  eapply (peutt_iter_direct_rel free_omega_relational_zero free_omega_relational_lub)
    with (SI := factory_states); [|reflexivity].
  intros [s' x] y <-.
  unfold lowered_step, factory_step, factory_sampler_step; cbn [fst snd].
  repeat setoid_rewrite lower_bind.
  setoid_rewrite lower_ret. setoid_rewrite peutt_bind_assoc.
  setoid_rewrite peutt_bind_ret_l.
  (* Relational bind retains the actual state on the implementation side. *)
  eapply peutt_bind with (RR := output_related); [apply adaptive_vn_fair|].
  intros [s'' b] c <-.
  apply peutt_ret. cbn [fst snd].
  destruct (binary_round_result x b); constructor; reflexivity.
Qed.

(** 4. Full-program calculation.

    Read this proof as: expose the State/interpreter loop; rewrite one whole
    request; replace the adaptive factory by its Bernoulli law; close the
    reactive iteration; remove the final identity bind. The two relational
    steps are explicit because successful state and bit are correlated. *)
Definition state_result {A} (sa : machine_state * A) (a : A) := snd sa = a.

Theorem controller_program_rewrite s q (q0 : 0 <= q) (q1 : q <= 1) :
  (sa <- run_state (PTree.interp internal_handler (controller q)) s;;
   Ret (snd sa)) ≈ₚ controller_spec q0 q1.
Proof.
  fold (lower (controller q) s).
  unfold controller. setoid_rewrite lower_iter.
  transitivity (a <- controller_spec q0 q1;; Ret a).
  - eapply peutt_bind with (RR := state_result).
    + unfold controller_spec.
      eapply (peutt_iter_direct_rel free_omega_relational_zero free_omega_relational_lub)
        with (SI := λ _ _, True); [|exact I].
      intros [s' []] [] _.
      (* One request, including its return to the outer loop. *)
      unfold lowered_step, serve_request, serve_spec; cbn [fst snd].
      unfold PTree.trigger.
      repeat setoid_rewrite lower_bind.
      setoid_rewrite lower_public. setoid_rewrite lower_ret.
      repeat setoid_rewrite peutt_bind_assoc.
      (* Distribute sequencing through events/sampling, then discharge Ret. *)
      repeat first [setoid_rewrite peutt_bind_vis
                   |setoid_rewrite peutt_bind_prob
                   |setoid_rewrite peutt_bind_ret_l].
      apply peutt_vis. intros [].
      (* Replace only the bit law; carry the sampled state to the next request. *)
      setoid_rewrite <- (peutt_sample_bind (bernoulli q0 q1)).
      eapply peutt_bind with (RR := output_related).
      * apply adaptive_factory_direct.
      * intros [s'' b] c <-.
        apply peutt_vis. intros []. apply peutt_ret. constructor. exact I.
    + intros sa a H. apply peutt_ret. exact H.
  - setoid_rewrite peutt_bind_ret_r. reflexivity.
Qed.

(** 5. Reusable consequences. The state-returning interfaces remain available;
    they are not used as shortcuts in the calculation above. *)
Theorem service_refinement s q (q0 : 0 <= q) (q1 : q <= 1) :
  lower (serve_request q) s ≈ₚ[state_result] serve_spec q0 q1.
Proof.
  unfold serve_request, serve_spec.
  unfold PTree.trigger.
  repeat setoid_rewrite lower_bind. setoid_rewrite lower_public.
  setoid_rewrite peutt_bind_vis. setoid_rewrite peutt_bind_ret_l.
  apply peutt_vis. intros [].
  eapply peutt_bind with (RR := output_related); [apply adaptive_factory_direct|].
  intros [s' b] c <-.
  apply peutt_vis. intros []. apply peutt_ret. reflexivity.
Qed.

Theorem controller_refinement s q (q0 : 0 <= q) (q1 : q <= 1) :
  lower (controller q) s ≈ₚ[state_result] controller_spec q0 q1.
Proof.
  eapply peutt_rel_compose with (R12 := state_result) (R23 := eq).
  - intros x y z H ->. exact H.
  - rewrite <- (peutt_bind_ret_r (lower (controller q) s)) at 1.
    eapply peutt_bind with (RR := eq); [reflexivity|].
    intros sa sa' ->. apply peutt_ret. reflexivity.
  - apply controller_program_rewrite.
Qed.

End Adaptive.
