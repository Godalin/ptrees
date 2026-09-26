(** Case role: paper case study.
    Reading entry: Adaptive.controller_program_rewrite.
    Native/frontier: EnumQ / observable FreeOmega; all primitive draws total.
    Internal effects are interpreted into State, then State is threaded out.
    State is NOT reset between attempts, factory iterations or requests.
    See docs/ADAPTIVE_FACTORY_CONTROLLER.md for the proved contract, mathematical boundaries and validation. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.
From Coq Require Import List Morphisms FunctionalExtensionality.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import EnumQ.
From PTree.Eq.FreeOmega Require Import Relation Hitting.
From PTree.Eq Require Import PTreeKernel UnifiedFrontier Shallow.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Observation Approximation StructuralMeasure
  SupportLift Quotient Measure RelationalLimit.
From PTree.Prob.Backend.EnumQ Require Import Measure Bind Iteration.
From PTree.Prob.Backend.Common Require Import FiniteEnum RatGeometric FiniteRecordExtensionality.
From PTree.Interp Require Import State StateIter.
From PTree.Interp Require Import Iteration IterationUniform.
From PTree.Interp.Algebra Require Import State Computation.
From PTree.Interp.FreeOmega Require Import Base Rewriting Unrestricted.
From PTree.Examples.BernoulliFactory Require Import
  VonNeumannUnbounded RationalBernoulli BernoulliFactory BernoulliFactoryComposition.
Import GRing.Theory Num.Theory Order.Theory FreeOmegaRewriting.
Local Open Scope ring_scope.

Module Adaptive.

(** Source identity is a Boolean, not the outcome of either sample. *)
Definition low_weight (src : bool) : rat := if src then 1/4 else 1/3.
Definition high_weight src : rat := 1 - low_weight src.
Lemma low_nonnegative src : 0 <= low_weight src.
Proof. destruct src; by vm_compute. Qed.
Lemma high_nonnegative src : 0 <= high_weight src.
Proof. destruct src; by vm_compute. Qed.
Definition source_coin src : EnumQ bool :=
  param_biased_coin (low_nonnegative src) (high_nonnegative src).

Record machine_state := MachineState {
  health : bool; retries : nat; repairs : nat; rounds : nat
}.
Definition initial_state := MachineState false 0 0 0.
Definition report_update s a :=
  MachineState (xorb (health s) a) (retries s) (repairs s) (rounds s).
Definition repair_update s :=
  MachineState (health s) (retries s) (S (repairs s)) (rounds s).
Definition retry_update s :=
  MachineState (health s) (S (retries s)) (repairs s) (rounds s).
Definition round_update s :=
  MachineState (health s) (retries s) (repairs s) (S (rounds s)).
Definition after_sensor s a :=
  if a then repair_update (report_update s a) else report_update s a.

Variant publicE : Type -> Type :=
| Request : publicE unit
| Emit : bool -> publicE unit.
Variant internalE : Type -> Type :=
| ChooseSource : internalE bool
| CheckSensor : bool -> internalE bool
| Maintenance : internalE unit
| Retry : internalE unit
| Round : internalE unit.
Definition implE := stateE machine_state +' (internalE +' publicE).
Definition targetE := stateE machine_state +' publicE.
Local Notation tree := (ptree implE EnumQ).

Definition internal {X} (e : internalE X) : tree X :=
  PTree.trigger (inr1 (inl1 e)).
Definition public {X} (e : publicE X) : tree X :=
  PTree.trigger (inr1 (inr1 e)).
Definition update (f : machine_state -> machine_state) : tree unit :=
  PTree.bind (Vis (inl1 (Get machine_state)) (fun s => Ret s))
    (fun s => Vis (inl1 (Put machine_state (f s))) (fun _ => Ret tt)).

Definition internal_handler X (e : implE X) : ptree targetE EnumQ X :=
  match e with
  | inl1 se => PTree.trigger (inl1 se)
  | inr1 (inr1 pe) => PTree.trigger (inr1 pe)
  | inr1 (inl1 ie) =>
    match ie with
    | ChooseSource => Vis (inl1 (Get machine_state)) (fun s => Ret (health s))
    | CheckSensor a => Ret a
    | Maintenance => Vis (inl1 (Get machine_state)) (fun s =>
        Vis (inl1 (Put machine_state (repair_update s))) (fun _ => Ret tt))
    | Retry => Vis (inl1 (Get machine_state)) (fun s =>
        Vis (inl1 (Put machine_state (retry_update s))) (fun _ => Ret tt))
    | Round => Vis (inl1 (Get machine_state)) (fun s =>
        Vis (inl1 (Put machine_state (round_update s))) (fun _ => Ret tt))
    end
  end.
Definition lower {A} (t : tree A) s := run_state (PTree.interp internal_handler t) s.

(** [src] is bound before either sample; changing health between them cannot
    change this attempt's second sampling distribution. *)
Definition vn_attempt (_ : unit) : tree (unit + bool) :=
  PTree.bind (internal ChooseSource) (fun src =>
  Prob (source_coin src) (fun a =>
  PTree.bind (internal (CheckSensor a)) (fun report =>
  PTree.bind (update (fun s => report_update s report)) (fun _ =>
  PTree.bind (if report then internal Maintenance else Ret tt) (fun _ =>
  Prob (source_coin src) (fun b =>
    if a == b then PTree.bind (internal Retry) (fun _ => Ret (inl tt))
    else Ret (inr a))))))).
Definition adaptive_vn : tree bool := PTree.iter vn_attempt tt.

Definition factory_step (x : rat) : tree (rat + bool) :=
  PTree.bind adaptive_vn (fun b =>
  PTree.bind (internal Round) (fun _ => Ret (binary_round_result x b))).
Definition eventful_factory q : tree bool := PTree.iter factory_step q.
Definition serve_request q : tree unit :=
  PTree.bind (public Request) (fun _ =>
  PTree.bind (eventful_factory q) (fun b => public (Emit b))).
Definition controller q : tree Empty_set :=
  PTree.iter (fun _ : unit => PTree.bind (serve_request q) (fun _ => Ret (inl tt))) tt.

Definition serve_spec q (q0 : 0 <= q) (q1 : q <= 1) : ptree publicE EnumQ unit :=
  Vis Request (fun _ => Prob (rational_bernoulli_measure q0 q1)
    (fun b => Vis (Emit b) (fun _ => Ret tt))).
Definition controller_spec q (q0 : 0 <= q) (q1 : q <= 1) :
    ptree publicE EnumQ Empty_set :=
  PTree.iter (fun _ : unit => PTree.bind (serve_spec q0 q1) (fun _ => Ret (inl tt))) tt.

(** Local interpretation equations; State is threaded, never erased. *)
Lemma lower_ret {A} (a : A) s : lower (Ret a) s ≈ₚ Ret (s,a).
Proof. apply peutt_observe_eq. reflexivity. Qed.

Lemma lower_bind {A B} (t : tree A) (k : A -> tree B) s :
  lower (PTree.bind t k) s ≈ₚ
  PTree.bind (lower t s) (fun sa => lower (k (snd sa)) (fst sa)).
Proof.
  unfold lower. setoid_rewrite peutt_interp_bind.
  apply peutt_of_pstruct.
  exact (@run_state_bind machine_state publicE EnumQ A B
    (PTree.interp internal_handler t) (fun x => PTree.interp internal_handler (k x)) s).
Qed.

Lemma lower_prob {A X} (mu : EnumQ X) (k : X -> tree A) s :
  lower (Prob mu k) s ≈ₚ Prob mu (fun x => lower (k x) s).
Proof.
  unfold lower. setoid_rewrite peutt_interp_prob.
  apply run_state_prob.
Qed.

Lemma lower_choose s : lower (internal ChooseSource) s ≈ₚ Ret (s,health s).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  apply peutt_observe_eq. reflexivity.
Qed.
Lemma lower_sensor a s : lower (internal (CheckSensor a)) s ≈ₚ Ret (s,a).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  apply peutt_observe_eq. reflexivity.
Qed.
Lemma lower_update f s : lower (update f) s ≈ₚ Ret (f s,tt).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  apply peutt_observe_eq. reflexivity.
Qed.
Lemma lower_maintenance s : lower (internal Maintenance) s ≈ₚ Ret (repair_update s,tt).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  apply peutt_observe_eq. reflexivity.
Qed.
Lemma lower_retry s : lower (internal Retry) s ≈ₚ Ret (retry_update s,tt).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  apply peutt_observe_eq. reflexivity.
Qed.

Definition state_attempt_result s a b : machine_state * (unit + bool) :=
  if a == b then (retry_update (after_sensor s a), inl tt)
  else (after_sensor s a, inr a).

Theorem lower_attempt s :
  lower (vn_attempt tt) s ≈ₚ
  Prob (source_coin (health s)) (fun a =>
    Prob (source_coin (health s)) (fun b => Ret (state_attempt_result s a b))).
Proof.
  unfold vn_attempt.
  setoid_rewrite lower_bind. setoid_rewrite lower_choose.
  setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite lower_prob.
  apply peutt_prob_Proper. intros a.
  setoid_rewrite lower_bind. setoid_rewrite lower_sensor.
  setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite lower_bind.
  setoid_rewrite lower_update. setoid_rewrite peutt_bind_ret_l.
  destruct a; cbn [fst snd].
  all: setoid_rewrite lower_bind.
  all: try setoid_rewrite lower_maintenance.
  all: try setoid_rewrite lower_ret.
  all: try setoid_rewrite peutt_bind_ret_l.
  all: setoid_rewrite lower_prob.
  all: apply peutt_prob_Proper; intros b; destruct b; cbn [fst snd].
  all: try setoid_rewrite lower_bind.
  all: try setoid_rewrite lower_retry.
  all: try setoid_rewrite peutt_bind_ret_l.
  all: setoid_rewrite lower_ret; reflexivity.
Qed.

(** Exact stateful kernel of one attempt. Successful states may depend on
    the returned bit; both failed states remain available to the retry. *)
Definition decode_attempt (sa : machine_state * (unit + bool)) :
    machine_state + (machine_state * bool) :=
  match snd sa with inl _ => inl (fst sa) | inr b => inr (fst sa,b) end.
Definition attempt_result s a b := decode_attempt (state_attempt_result s a b).
Definition attempt_kernel s : EnumQ (machine_state + (machine_state * bool)) :=
  sem_bind (source_coin (health s)) (fun a =>
    sem_bind (source_coin (health s)) (fun b => sem_ret (attempt_result s a b))).

Theorem lower_attempt_kernel s :
  PTree.bind (lower (vn_attempt tt) s) (fun sa => Ret (decode_attempt sa)) ≈ₚ
  Prob (attempt_kernel s) (fun result => Ret result).
Proof.
  setoid_rewrite lower_attempt.
  setoid_rewrite peutt_bind_prob.
  setoid_rewrite peutt_bind_prob.
  setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite (peutt_sample_map (MF := FreeOmega EnumQ) (source_coin (health s))).
  setoid_rewrite peutt_prob_flatten.
  reflexivity.
Qed.

(** Infinite-loop normalization is an algebraic consumer of the attempt
    calculation. It retains all state; fairness is proved separately below. *)
Definition normalized_step (si : machine_state * unit) :
    ptree publicE EnumQ ((machine_state * unit) + (machine_state * bool)) :=
  Prob (source_coin (health (fst si))) (fun a =>
  Prob (source_coin (health (fst si))) (fun b =>
    Ret (state_iter_result (state_attempt_result (fst si) a b)))).

Lemma normalized_step_correct si :
  state_iter_step (fun i => PTree.interp internal_handler (vn_attempt i)) si ≈ₚ
  normalized_step si.
Proof.
  destruct si as [s []].
  change (PTree.bind (lower (vn_attempt tt) s)
    (fun sa => Ret (state_iter_result sa)) ≈ₚ normalized_step (s,tt)).
  setoid_rewrite lower_attempt.
  setoid_rewrite peutt_bind_prob. setoid_rewrite peutt_bind_prob.
  setoid_rewrite peutt_bind_ret_l. reflexivity.
Qed.

Theorem lower_adaptive_normalized s :
  lower adaptive_vn s ≈ₚ PTree.iter normalized_step (s,tt).
Proof.
  unfold lower, adaptive_vn. setoid_rewrite peutt_interp_iter.
  transitivity (PTree.iter
    (state_iter_step (fun i => PTree.interp internal_handler (vn_attempt i))) (s,tt)).
  - apply peutt_of_pstruct.
    exact (@run_state_iter machine_state unit bool publicE EnumQ
      (fun i => PTree.interp internal_handler (vn_attempt i)) tt s).
  - setoid_rewrite (normalized_step_correct : pointwise_relation _
      (fun t u => t ≈ₚ u) _ _). reflexivity.
Qed.

Lemma source_expect src (f : bool -> rat) :
  enumQ_expect f (source_coin src) =
    low_weight src * f false + high_weight src * f true.
Proof.
  rewrite /source_coin /param_biased_coin !enumQ_expect_cons enumQ_expect_nil addr0.
  reflexivity.
Qed.

Lemma attempt_expect s (f : machine_state + (machine_state * bool) -> rat) :
  enumQ_expect f (attempt_kernel s) =
    low_weight (health s) *
      (low_weight (health s) * f (inl (retry_update (after_sensor s false))) +
       high_weight (health s) * f (inr (after_sensor s false, false))) +
    high_weight (health s) *
      (low_weight (health s) * f (inr (after_sensor s true, true)) +
       high_weight (health s) * f (inl (retry_update (after_sensor s true)))).
Proof.
  cbn [attempt_kernel sem_bind sem_ret EnumQ_SemanticMeasure].
  rewrite enumQ_expect_bind source_expect.
  rewrite !enumQ_expect_bind !source_expect.
  rewrite !enumQ_expect_ret. reflexivity.
Qed.

(** A complete finite experiment: inl means all n attempts failed, inr means
    success with its actual state. This is not internal-node fuel. *)
Fixpoint attempts (n : nat) s : EnumQ (machine_state + (machine_state * bool)) :=
  match n with
  | O => sem_ret (inl s)
  | S k => sem_bind (attempt_kernel s) (fun result =>
      match result with inl s' => attempts k s' | inr sb => sem_ret (inr sb) end)
  end.
Definition pending (x : machine_state + (machine_state * bool)) : rat :=
  match x with inl _ => 1 | inr _ => 0 end.
Definition returns (b : bool) (x : machine_state + (machine_state * bool)) : rat :=
  match x with inl _ => 0 | inr sb => if snd sb == b then 1 else 0 end.

Lemma attempts_expect_S n s f :
  enumQ_expect f (attempts (S n) s) =
    low_weight (health s) *
      (low_weight (health s) * enumQ_expect f (attempts n (retry_update (after_sensor s false))) +
       high_weight (health s) * f (inr (after_sensor s false, false))) +
    high_weight (health s) *
      (low_weight (health s) * f (inr (after_sensor s true, true)) +
       high_weight (health s) * enumQ_expect f (attempts n (retry_update (after_sensor s true)))).
Proof.
  cbn [attempts sem_bind sem_ret EnumQ_SemanticMeasure].
  rewrite enumQ_expect_bind attempt_expect /= !enumQ_expect_ret. reflexivity.
Qed.

Lemma attempts_pending_S n s :
  enumQ_expect pending (attempts (S n) s) =
    low_weight (health s) ^+ 2 * enumQ_expect pending (attempts n (retry_update (after_sensor s false))) +
    high_weight (health s) ^+ 2 * enumQ_expect pending (attempts n (retry_update (after_sensor s true))).
Proof.
  rewrite attempts_expect_S /pending !mulr0 addr0 add0r !mulrA.
  by rewrite !expr2.
Qed.

Lemma retry_bound src : low_weight src ^+ 2 + high_weight src ^+ 2 <= (5/8 : rat).
Proof. destruct src; by vm_compute. Qed.

Lemma source_normalized src : low_weight src + high_weight src = 1.
Proof. rewrite /high_weight addrC subrK. reflexivity. Qed.

Theorem attempts_total n s : enumQ_expect (fun _ => 1) (attempts n s) = 1.
Proof.
  elim: n s => [|n IH] s; first reflexivity.
  rewrite attempts_expect_S !IH !mulr1 source_normalized !mulr1 source_normalized.
  reflexivity.
Qed.

Theorem attempts_symmetric n s :
  enumQ_expect (returns false) (attempts n s) =
  enumQ_expect (returns true) (attempts n s).
Proof.
  elim: n s => [|n IH] s; first reflexivity.
  rewrite !attempts_expect_S /returns /= !mulr0 !mulr1 !addr0 !add0r.
  rewrite !mulrDr !mulrA -!addrA.
  rewrite -/(returns false) -/(returns true) !IH.
  by rewrite /high_weight !mulrDl !mul1r !mulNr !mulrN !mulr1 -!addrA.
Qed.

Theorem adaptive_pending_bound n s :
  enumQ_expect pending (attempts n s) <= (5/8 : rat) ^+ n.
Proof.
  elim: n s => [|n IH] s.
  - change ((1 : rat) <= 1). exact: lexx.
  - rewrite attempts_pending_S (exprS (5/8 : rat) n).
    have Hl := ler_wpM2l (exprn_ge0 2 (low_nonnegative (health s)))
      (IH (retry_update (after_sensor s false))).
    have Hr := ler_wpM2l (exprn_ge0 2 (high_nonnegative (health s)))
      (IH (retry_update (after_sensor s true))).
    apply: le_trans (lerD Hl Hr) _.
    rewrite -mulrDl.
    have Hbase : (0 : rat) <= 5/8 by vm_compute.
    exact: (ler_wpM2r (exprn_ge0 n Hbase) (retry_bound (health s))).
Qed.

Theorem adaptive_pending_vanishes s eps : 0 < eps ->
  exists N, forall n, (N <= n)%coq_nat -> enumQ_expect pending (attempts n s) < eps.
Proof.
  intro Heps.
  have Hpos : (0 < 2)%coq_nat by repeat constructor.
  have Hnonneg : (0 : rat) <= 5/8 by vm_compute.
  have Hcontract : (5/8 : rat) <= 2%:R / 3%:R by vm_compute.
  destruct (rat_contract_vanishes Hpos Hnonneg Hcontract Heps) as [N HN].
  exists N. intros n Hn. exact: le_lt_trans (adaptive_pending_bound n s) (HN n Hn).
Qed.

Theorem attempts_partition n s :
  enumQ_expect (returns false) (attempts n s) +
  enumQ_expect (returns true) (attempts n s) +
  enumQ_expect pending (attempts n s) = 1.
Proof.
  have H : enumQ_expect (fun x => returns false x + returns true x + pending x)
      (attempts n s) = 1.
  { transitivity (enumQ_expect (fun _ => 1) (attempts n s)).
    - apply finite_expect_ext. intros [s'|[s' b]]; first reflexivity.
      destruct b; by vm_compute.
    - apply attempts_total. }
  move: H. rewrite /enumQ_expect /finite_enum_expect !finite_expect_add.
  exact (fun H => H).
Qed.

Theorem attempts_return_probability n s b :
  enumQ_expect (returns b) (attempts n s) =
    (1 - enumQ_expect pending (attempts n s)) / 2.
Proof.
  have H := attempts_partition n s.
  have Hsym := attempts_symmetric n s.
  destruct b.
  - rewrite Hsym in H.
    apply (mulIf (x := (2 : rat))); first by vm_compute.
    rewrite divrK; last by vm_compute.
    apply: (addIr (enumQ_expect pending (attempts n s))).
    rewrite subrK mulr_natr mulr2n. exact H.
  - rewrite -Hsym in H.
    apply (mulIf (x := (2 : rat))); first by vm_compute.
    rewrite divrK; last by vm_compute.
    apply: (addIr (enumQ_expect pending (attempts n s))).
    rewrite subrK mulr_natr mulr2n. exact H.
Qed.

Theorem adaptive_return_limit s b eps : 0 < eps ->
  exists N, forall n, (N <= n)%coq_nat ->
    `|enumQ_expect (returns b) (attempts n s) - (1/2 : rat)| < eps.
Proof.
  intro Heps. destruct (adaptive_pending_vanishes s Heps) as [N HN].
  exists N. intros n Hn.
  have Htail : 0 <= enumQ_expect pending (attempts n s).
  { apply finite_expect_nonnegative; first exact (enumQ_nonnegative (attempts n s)).
    intros [s'|sb]; by vm_compute. }
  rewrite attempts_return_probability vn_difference normrN normrM (ger0_norm Htail).
  have Hhalf : `|(1/2 : rat)| <= 1 by vm_compute.
  have Hle := ler_wpM2l Htail Hhalf.
  rewrite mulr1 in Hle. exact: le_lt_trans Hle (HN n Hn).
Qed.

(** Boundary checks: adaptation is real, and successful state is correlated
    with the returned bit. Neither fact is silently erased by the analysis. *)
Example retry_can_switch_source :
  health initial_state = false /\
  health (retry_update (after_sensor initial_state true)) = true.
Proof. split; reflexivity. Qed.
Example successful_states_distinct :
  after_sensor initial_state false <> after_sensor initial_state true.
Proof. discriminate. Qed.
Example different_retry_rates :
  low_weight false ^+ 2 + high_weight false ^+ 2 <
  low_weight true ^+ 2 + high_weight true ^+ 2.
Proof. by vm_compute. Qed.

(** Count complete attempts, rather than primitive internal steps. The
    observer rejects visible heads; None is never part of the limit law. *)
Definition bit_observer {A} (value : A -> bool)
    (h : stable_head publicE EnumQ A) : option bool :=
  match h with FHRet a => Some (value a) | FHVis _ _ _ => None end.
Definition raw_loop s := PTree.iter normalized_step (s,tt).
Definition loop_after (next : (machine_state * unit) + (machine_state * bool)) :=
  match next with inl si => Tau (PTree.iter normalized_step si)
  | inr sb => Ret sb end.
Definition loop_second s a :=
  PTree.bind (Prob (source_coin (health s)) (fun b =>
    Ret (state_iter_result (state_attempt_result s a b)))) loop_after.
Lemma raw_loop_observe s :
  observe (raw_loop s) = ProbF (source_coin (health s)) (loop_second s).
Proof.
  unfold raw_loop. rewrite (observing_observe (unfold_aloop_ normalized_step (s,tt))).
  rewrite observe_bind. reflexivity.
Qed.
Definition loop_hitting n s := ptree_hitting_approx
  (MF := FreeOmega EnumQ) n (observe (raw_loop s)).
Lemma loop_second_observe s a : observe (loop_second s a) =
  ProbF (source_coin (health s)) (fun b =>
    PTree.bind (Ret (state_iter_result (state_attempt_result s a b))) loop_after).
Proof. unfold loop_second. rewrite observe_bind. reflexivity. Qed.
Lemma loop_hitting_three n s :
  loop_hitting (S (S (S n))) s =
  FOSample (source_coin (health s)) (fun a =>
  FOSample (source_coin (health s)) (fun b =>
    if a == b then loop_hitting n (retry_update (after_sensor s a))
    else FORet (FHRet (after_sensor s a,a)))).
Proof.
  unfold loop_hitting. rewrite raw_loop_observe.
  cbn [ptree_hitting_approx ptree_primitive_kernel ptree_stable_target_approx
    stable_hitting_approx stable_target_approx sem_bind sem_ret mixed_bind
    free_omega_bind FreeOmegaMixedMeasure FreeOmegaObservableSemanticMeasure].
  f_equal. apply functional_extensionality=> a.
  rewrite loop_second_observe.
  cbn [ptree_primitive_kernel ptree_stable_target_approx stable_target_approx
    sem_bind sem_ret mixed_bind free_omega_bind FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticMeasure].
  f_equal. apply functional_extensionality=> b. rewrite observe_bind.
  destruct a, b; reflexivity.
Qed.
Fixpoint round_schedule n :=
  match n with O => O | S k => S (S (S (round_schedule k))) end.
Lemma round_schedule_ge n : (n <= round_schedule n)%coq_nat.
Proof. induction n; cbn; [constructor|apply le_n_S; apply le_S, le_S; assumption]. Qed.
Lemma round_schedule_mono n : (round_schedule n <= round_schedule (S n))%coq_nat.
Proof. cbn. repeat apply le_S. constructor. Qed.
Fixpoint output_row n s : EnumQ (option bool) :=
  match n with
  | O => enumQ_zero
  | S k => sem_bind (source_coin (health s)) (fun a =>
      sem_bind (source_coin (health s)) (fun b =>
        if a == b then output_row k (retry_update (after_sensor s a))
        else sem_ret (Some a)))
  end.
Lemma loop_hitting_observes n s :
  free_omega_observes (bit_observer (@snd machine_state bool))
    (loop_hitting (round_schedule n) s) (output_row n s).
Proof.
  revert s. induction n as [|n IH]; intro s.
  - unfold loop_hitting. rewrite raw_loop_observe.
    change (free_omega_observes (bit_observer (@snd machine_state bool))
      (FOSample (source_coin (health s)) (fun _ => FOZero)) enumQ_zero).
    replace (@enumQ_zero (option bool)) with
      (bind_EnumQ (source_coin (health s)) (fun _ => @enumQ_zero (option bool)))
      by apply finite_enum_bind_zero_eq.
    constructor. intro a. constructor.
  - cbn [round_schedule output_row]. rewrite loop_hitting_three.
    constructor. intro a. constructor. intro b.
    destruct a,b.
    + exact (IH (retry_update (after_sensor s true))).
    + constructor.
    + constructor.
    + exact (IH (retry_update (after_sensor s false))).
Qed.
Definition loop_heads s := FOLub (fun n => loop_hitting (round_schedule n) s).
Lemma loop_hits s : ptree_stable_hitting (MF := FreeOmega EnumQ)
    (observe (raw_loop s)) (loop_heads s).
Proof. exact (stable_hitting_subsequence (raw_loop s) round_schedule_mono round_schedule_ge). Qed.

Lemma output_row_expect n s f : enumQ_expect f (output_row n s) =
  enumQ_expect (fun z => match z with inl _ => 0 | inr sb => f (Some (snd sb)) end)
    (attempts n s).
Proof.
  revert s. induction n as [|n IH]; intro s.
  - reflexivity.
  - rewrite attempts_expect_S.
    cbn [output_row sem_bind sem_ret EnumQ_SemanticMeasure].
    rewrite enumQ_expect_bind source_expect !enumQ_expect_bind !source_expect.
    rewrite ?enumQ_expect_ret !IH. reflexivity.
Qed.
Definition fair_options : EnumQ (option bool) :=
  sem_bind vn_fair (fun b => sem_ret (Some b)).
Lemma fair_options_expect f : enumQ_expect f fair_options =
  (1/2 : rat) * (f (Some false) + f (Some true)).
Proof.
  change (enumQ_expect f (bind_EnumQ vn_fair (fun b => ret_EnumQ (Some b))) =
    (1/2 : rat) * (f (Some false) + f (Some true))).
  rewrite enumQ_expect_bind. unfold vn_fair.
  rewrite enumQ_expect_unif2 !enumQ_expect_ret /one_div_two mulrDr addr0. reflexivity.
Qed.
Lemma output_row_factor n s f : enumQ_expect f (output_row n s) =
  (1 - enumQ_expect pending (attempts n s)) * enumQ_expect f fair_options.
Proof.
  rewrite output_row_expect.
  transitivity (enumQ_expect (fun z =>
    f (Some false) * returns false z + f (Some true) * returns true z) (attempts n s)).
  - apply finite_expect_ext. intros [s'|[s' b]]; [|destruct b];
      cbn [returns snd]; rewrite ?mulr0 ?mulr1 ?addr0 ?add0r; reflexivity.
  - unfold enumQ_expect, finite_enum_expect.
    erewrite finite_expect_add. erewrite finite_expect_scale. erewrite finite_expect_scale.
    change (f (Some false) * enumQ_expect (returns false) (attempts n s) +
      f (Some true) * enumQ_expect (returns true) (attempts n s) =
      (1 - enumQ_expect pending (attempts n s)) * enumQ_expect f fair_options).
    rewrite !attempts_return_probability fair_options_expect.
    by rewrite -mulrDl mulrC -mulrA.
Qed.
Lemma output_row_converges s :
  enumQ_converges (fun n => output_row n s) fair_options.
Proof.
  intros P eps Heps. destruct (adaptive_pending_vanishes s Heps) as [N HN].
  exists N. intros n Hn.
  rewrite output_row_factor vn_difference normrN normrM.
  have Htail : 0 <= enumQ_expect pending (attempts n s).
  { apply finite_expect_nonnegative; first exact (enumQ_nonnegative (attempts n s)).
    intros [s'|sb]; by vm_compute. }
  rewrite (ger0_norm Htail).
  have Hbound : `|enumQ_expect (fun x => if P x then 1 else 0) fair_options| <= 1.
  { rewrite fair_options_expect. destruct (P (Some false)), (P (Some true)); by vm_compute. }
  have Hle := ler_wpM2l Htail Hbound. rewrite mulr1 in Hle.
  apply: le_lt_trans Hle _. exact (HN n Hn).
Qed.
Lemma loop_heads_observes s :
  free_omega_observes (bit_observer (@snd machine_state bool)) (loop_heads s) fair_options.
Proof.
  eapply FOOObserveLub.
  - intro n. exact (loop_hitting_observes n s).
  - exact (output_row_converges s).
  - intro n. unfold loop_hitting.
    apply (ptree_hitting_mono (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)). apply round_schedule_mono.
Qed.

Lemma source_ae_inv src P : sem_ae (source_coin src) P -> forall b, P b.
Proof.
  intros H b. destruct b.
  - apply H with (p := high_weight src).
    + cbn. auto.
    + destruct src; vm_compute; discriminate.
  - apply H with (p := low_weight src).
    + cbn. auto.
    + destruct src; vm_compute; discriminate.
Qed.
Lemma fair_ae_inv P : sem_ae vn_fair P -> forall b, P b.
Proof.
  intros H b. apply H with (p := one_div_two).
  - destruct b; cbn; auto.
  - vm_compute; discriminate.
Qed.
Definition fair_tree : ptree publicE EnumQ bool := Prob vn_fair (fun b => Ret b).
Definition fair_heads : FreeOmega EnumQ (stable_head publicE EnumQ bool) :=
  FOSample vn_fair (fun b => FORet (FHRet b)).
Lemma fair_hits : ptree_stable_hitting (MF := FreeOmega EnumQ)
  (observe fair_tree) fair_heads.
Proof.
  unfold fair_tree, fair_heads.
  change (ptree_stable_hitting (E := publicE) (MN := EnumQ) (MF := FreeOmega EnumQ)
    (ProbF vn_fair (fun b => Ret b))
    (mixed_bind vn_fair (fun b => FORet (FHRet b)))).
  eapply (ptree_stable_hitting_prob (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. apply (ptree_stable_hitting_ret (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)).
Qed.
Lemma fair_heads_observes :
  free_omega_observes (bit_observer (fun b => b)) fair_heads fair_options.
Proof. constructor. intro b. constructor. Qed.
Lemma loop_heads_returns s : free_omega_ae
    (fun h => exists sb, h = FHRet sb) (loop_heads s).
Proof.
  constructor. intro n. revert s. induction n as [|n IH]; intro s.
  - unfold loop_hitting. rewrite raw_loop_observe.
    change (free_omega_ae (fun h : stable_head publicE EnumQ (machine_state * bool) =>
      exists sb, h = FHRet sb) (FOSample (source_coin (health s)) (fun _ => FOZero))).
    eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros b _. constructor.
  - cbn [round_schedule]. rewrite loop_hitting_three.
    eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros a _. eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros b _. destruct a,b.
    + exact (IH _).
    + constructor. eexists. reflexivity.
    + constructor. eexists. reflexivity.
    + exact (IH _).
Qed.
Lemma loop_heads_success s P : free_omega_ae P (loop_heads s) ->
  forall b, P (FHRet (after_sensor s b,b)).
Proof.
  intro HP. unfold loop_heads in HP. dependent destruction HP.
  specialize (H 1%nat). cbn [round_schedule] in H.
  rewrite loop_hitting_three in H.
  pose proof (source_ae_inv (free_omega_ae_sample_inv H)) as Hfirst.
  intro b. specialize (Hfirst b).
  pose proof (source_ae_inv (free_omega_ae_sample_inv Hfirst) (negb b)) as Hsecond.
  destruct b; cbn in Hsecond; dependent destruction Hsecond; assumption.
Qed.
Definition output_related (sb : machine_state * bool) (b : bool) := snd sb = b.
Lemma loop_heads_fair_support s sim :
  free_omega_support_lift (stable_head_rel output_related sim) (loop_heads s) fair_heads.
Proof.
  split.
  - intros P HP. eapply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
    intros b _. constructor. exists (FHRet (after_sensor s b,b)). split.
    + constructor. reflexivity.
    + exact (loop_heads_success HP b).
  - intros Q HQ. pose proof (fair_ae_inv (free_omega_ae_sample_inv HQ)) as HQb.
    eapply free_omega_ae_mono; [|exact (loop_heads_returns s)].
    intros h [sb ->]. exists (FHRet (snd sb)). split; [constructor; reflexivity|].
    specialize (HQb (snd sb)). inversion HQb; subst; assumption.
Qed.
Lemma loop_heads_fair_lift s sim :
  free_omega_qlift (stable_head_rel output_related sim) (loop_heads s) fair_heads.
Proof.
  eapply FOQLObserve with
    (obsA := bit_observer (@snd machine_state bool))
    (obsB := bit_observer (fun b => b))
    (outA := fair_options) (outB := fair_options)
    (S := fun x y => exists b, x = Some b /\ y = Some b).
  - exact (loop_heads_observes s).
  - exact fair_heads_observes.
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
  - exact fair_hits.
  - exact (loop_heads_fair_lift s _).
Qed.

Theorem adaptive_vn_fair s : lower adaptive_vn s ≈ₚ[output_related] fair_tree.
Proof.
  eapply Iteration.iteration_peutt_compose with (R12 := eq) (R23 := output_related).
  - intros x y b -> H. exact H.
  - exact (lower_adaptive_normalized s).
  - exact (raw_loop_fair s).
Qed.
Theorem raw_loop_ast s : ptree_stable_hitting_ast (MF := FreeOmega EnumQ)
  (observe (raw_loop s)) (loop_heads s).
Proof.
  split; [apply loop_hits|]. apply free_omega_observable_total_intro.
  exists (option bool), (bit_observer (@snd machine_state bool)), fair_options.
  split; [apply loop_heads_observes|].
  change (enumQ_expect (fun _ => 1) fair_options = 1).
  rewrite fair_options_expect. by vm_compute.
Qed.

(** From here on, the analytic certificate is consumed through program
    relations; no finite list or rational-limit calculation is repeated. *)
Definition lowered_step {I A} (step : I -> tree (I+A)) (si : machine_state * I) :=
  PTree.bind (lower (step (snd si)) (fst si)) (fun sa => Ret (state_iter_result sa)).
Lemma lower_iter {I A} (step : I -> tree (I+A)) i s :
  lower (PTree.iter step i) s ≈ₚ PTree.iter (lowered_step step) (s,i).
Proof.
  unfold lower. setoid_rewrite peutt_interp_iter.
  apply peutt_of_pstruct.
  exact (@run_state_iter machine_state I A publicE EnumQ
    (fun i => PTree.interp internal_handler (step i)) i s).
Qed.
Lemma lower_round s : lower (internal Round) s ≈ₚ Ret (round_update s,tt).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  apply peutt_observe_eq. reflexivity.
Qed.
Lemma lower_factory_step s q : lowered_step factory_step (s,q) ≈ₚ
  PTree.bind (lower adaptive_vn s) (fun sb =>
    Ret (state_iter_result (round_update (fst sb), binary_round_result q (snd sb)))).
Proof.
  unfold lowered_step, factory_step. cbn [fst snd].
  setoid_rewrite lower_bind. setoid_rewrite lower_bind.
  setoid_rewrite lower_round. setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite lower_ret. setoid_rewrite peutt_bind_assoc.
  setoid_rewrite peutt_bind_ret_l. reflexivity.
Qed.
Definition factory_states (si : machine_state * rat) q := snd si = q.
Lemma factory_step_related si q : factory_states si q ->
  lowered_step factory_step si ≈ₚ[pstruct_iter_sum_rel factory_states output_related]
    factory_sampler_step fair_tree q.
Proof.
  destruct si as [s x]. intros <-.
  eapply Iteration.iteration_peutt_compose with (R12 := eq)
    (R23 := pstruct_iter_sum_rel factory_states output_related).
  - intros r r' z -> H. exact H.
  - apply lower_factory_step.
  - unfold factory_sampler_step. eapply peutt_bind with (RR := output_related).
    + apply adaptive_vn_fair.
    + intros [s' b] c Hbc. unfold output_related in Hbc. cbn in Hbc. subst c.
      apply peutt_ret. cbn [fst snd].
      destruct (binary_round_result x b); constructor; reflexivity.
Qed.
Theorem adaptive_factory_fair s q : lower (eventful_factory q) s ≈ₚ[output_related]
    factory_with_sampler fair_tree q.
Proof.
  eapply Iteration.iteration_peutt_compose with (R12 := eq) (R23 := output_related).
  - intros x y b -> H. exact H.
  - apply lower_iter.
  - eapply (peutt_iter_direct_rel free_omega_relational_zero free_omega_relational_lub)
      with (SI := factory_states).
    + exact factory_step_related.
    + reflexivity.
Qed.

Definition embed_closed {A} (t : ptree factoryE EnumQ A) : ptree publicE EnumQ A :=
  PTree.interp (fun X (e : factoryE X) => match e with end) t.
Lemma fair_factory_direct q (q0 : 0 <= q) (q1 : q <= 1) :
  factory_with_sampler fair_tree q ≈ₚ
    Prob (rational_bernoulli_measure q0 q1) (fun b => Ret b).
Proof.
  have H : embed_closed (factory_with_sampler factory_direct_fair q) ≈ₚ
      embed_closed (factory_direct_q q0 q1).
  { apply peutt_interp. exact (peutt_factory_fair_direct q0 q1). }
  unfold embed_closed, factory_with_sampler, factory_sampler_step,
    factory_direct_fair, factory_direct_q in H.
  setoid_rewrite peutt_interp_iter in H.
  setoid_rewrite peutt_interp_bind in H.
  setoid_rewrite peutt_interp_prob in H.
  setoid_rewrite peutt_interp_ret in H.
  exact H.
Qed.
Theorem adaptive_factory_direct s q (q0 : 0 <= q) (q1 : q <= 1) :
  lower (eventful_factory q) s ≈ₚ[output_related]
    Prob (rational_bernoulli_measure q0 q1) (fun b => Ret b).
Proof.
  eapply Iteration.iteration_peutt_compose with (R12 := output_related) (R23 := eq).
  - intros sb b c H ->. exact H.
  - apply adaptive_factory_fair.
  - apply fair_factory_direct.
Qed.
Lemma lower_public {X} (e : publicE X) s :
  lower (public e) s ≈ₚ Vis e (fun x => Ret (s,x)).
Proof.
  repeat (eapply peutt_tau_step; [cbn; reflexivity|]).
  transitivity (Vis e (fun x => run_state
    (PTree.bind (Ret x) (fun y => PTree.interp internal_handler (Ret y))) s)).
  - apply peutt_observe_eq. reflexivity.
  - apply peutt_vis. intro x. apply peutt_observe_eq. reflexivity.
Qed.
Lemma lower_service s q : lower (serve_request q) s ≈ₚ
  Vis Request (fun _ =>
    PTree.bind (lower (eventful_factory q) s) (fun sb =>
      Vis (Emit (snd sb)) (fun ack => Ret (fst sb,ack)))).
Proof.
  unfold serve_request. setoid_rewrite lower_bind.
  setoid_rewrite lower_public. setoid_rewrite peutt_bind_vis.
  setoid_rewrite peutt_bind_ret_l.
  setoid_rewrite lower_bind. setoid_rewrite lower_public. reflexivity.
Qed.
Definition state_result {A} (sa : machine_state * A) (a : A) := snd sa = a.
Theorem service_refinement s q (q0 : 0 <= q) (q1 : q <= 1) :
  lower (serve_request q) s ≈ₚ[state_result] serve_spec q0 q1.
Proof.
  eapply Iteration.iteration_peutt_compose with (R12 := eq) (R23 := state_result).
  - intros x y z -> H. exact H.
  - apply lower_service.
  - apply peutt_vis. intros [].
    eapply Iteration.iteration_peutt_compose with (R12 := state_result) (R23 := eq).
    + intros x y z H ->. exact H.
    + eapply peutt_bind with (RR := output_related)
        (k2 := fun b => Vis (Emit b) (fun _ => Ret tt)).
      * exact (adaptive_factory_direct s q0 q1).
      * intros [s' b] c H. unfold output_related in H. cbn in H. subst c.
        cbn [fst snd]. apply peutt_vis. intros []. apply peutt_ret. reflexivity.
    + setoid_rewrite peutt_bind_prob. setoid_rewrite peutt_bind_ret_l. reflexivity.
Qed.
Definition service_iteration q (_ : unit) : tree (unit + Empty_set) :=
  PTree.bind (serve_request q) (fun _ => Ret (inl tt)).
Definition spec_iteration q (q0 : 0 <= q) (q1 : q <= 1) (_ : unit) :
    ptree publicE EnumQ (unit + Empty_set) :=
  PTree.bind (serve_spec q0 q1) (fun _ => Ret (inl tt)).
Lemma lower_service_iteration s q : lowered_step (service_iteration q) (s,tt) ≈ₚ
  PTree.bind (lower (serve_request q) s) (fun su => Ret (inl (fst su,tt))).
Proof.
  unfold lowered_step, service_iteration. cbn [fst snd].
  setoid_rewrite (lower_bind (serve_request q)
    (fun _ => Ret (inl tt : unit + Empty_set)) s).
  setoid_rewrite lower_ret.
  setoid_rewrite peutt_bind_assoc. setoid_rewrite peutt_bind_ret_l. reflexivity.
Qed.
Lemma service_iteration_related q (q0 : 0 <= q) (q1 : q <= 1) si u :
  lowered_step (service_iteration q) si ≈ₚ[
    pstruct_iter_sum_rel (fun _ _ => True) state_result] spec_iteration q0 q1 u.
Proof.
  destruct si as [s []], u.
  eapply Iteration.iteration_peutt_compose with (R12 := eq)
    (R23 := pstruct_iter_sum_rel (fun _ _ => True) state_result).
  - intros x y z -> H. exact H.
  - apply lower_service_iteration.
  - unfold spec_iteration. eapply peutt_bind with (RR := state_result).
    + exact (service_refinement s q0 q1).
    + intros [s' []] [] _. apply peutt_ret. constructor. exact I.
Qed.
Theorem controller_refinement s q (q0 : 0 <= q) (q1 : q <= 1) :
  lower (controller q) s ≈ₚ[state_result] controller_spec q0 q1.
Proof.
  eapply Iteration.iteration_peutt_compose with (R12 := eq) (R23 := state_result).
  - intros x y z -> H. exact H.
  - apply lower_iter.
  - eapply (peutt_iter_direct_rel free_omega_relational_zero free_omega_relational_lub)
      with (SI := fun _ _ => True).
    + intros si u _. exact (service_iteration_related q0 q1 si u).
    + exact I.
Qed.
Theorem controller_program_rewrite s q (q0 : 0 <= q) (q1 : q <= 1) :
  PTree.bind (run_state (PTree.interp internal_handler (controller q)) s)
    (fun sa => Ret (snd sa)) ≈ₚ controller_spec q0 q1.
Proof.
  change (PTree.bind (lower (controller q) s) (fun sa => Ret (snd sa)) ≈ₚ
    controller_spec q0 q1).
  unfold controller. setoid_rewrite lower_iter.
  transitivity (PTree.bind (controller_spec q0 q1) (fun a => Ret a)).
  - eapply peutt_bind with (RR := state_result).
    + eapply (peutt_iter_direct_rel free_omega_relational_zero free_omega_relational_lub)
        with (SI := fun _ _ => True).
      * intros si u _. exact (service_iteration_related q0 q1 si u).
      * exact I.
    + intros sa a H. apply peutt_ret. exact H.
  - setoid_rewrite peutt_bind_ret_r. reflexivity.
Qed.

End Adaptive.
