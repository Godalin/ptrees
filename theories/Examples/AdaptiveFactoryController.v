(** Case role: paper case study, under construction.
    Native/frontier: EnumQ / observable FreeOmega; all primitive draws total.
    Internal effects are interpreted into State, then State is threaded out.
    State is NOT reset between attempts, factory iterations or requests.
    See docs/ADAPTIVE_FACTORY_CONTROLLER.md for established endpoints and gaps. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.
From Coq Require Import List Morphisms.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import EnumQ.
From PTree.Eq.FreeOmega Require Import Relation.
From PTree.Prob.Interface Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.Backend.EnumQ Require Import Measure Bind.
From PTree.Prob.Backend.Common Require Import FiniteEnum RatGeometric.
From PTree.Interp Require Import State StateIter.
From PTree.Interp.Algebra Require Import State Computation.
From PTree.Interp.FreeOmega Require Import Base Rewriting.
From PTree.Examples.BernoulliFactory Require Import
  VonNeumannUnbounded RationalBernoulli BernoulliFactory.
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
    calculation. It retains all state, and does NOT yet replace retry by Fair. *)
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

End Adaptive.
