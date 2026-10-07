(** Role: concrete execution and resource-outcome example. *)
(** A single vertical-slice regression: independent device replies, State,
    exact visible probabilities and the same extracted infinite program. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ ProbabilisticTraceSubEnumQ.
From PTree.Interp Require Import State.
From PTree.Examples.BernoulliFactory Require Import BernoulliFactory BoundedFactory.
From PTree.Examples Require Import FactoryController.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope subenumQ_probability_scope.
Set Default Timeout 20.

(** Expose only the next operational node, then use the public Tau/Vis laws. *)
Ltac expose_left :=
  lazymatch goal with
  | |- ?R ?t ?v =>
    let u := eval cbn in (go (observe t)) in
    transitivity u; [apply PTree.Eq.Algebra.peutt_observe_eq; reflexivity|]
  end.

(** Positive source weights do not exclude deterministic target probabilities.
    No separate source nonnegativity or product-positivity premise is needed. *)
Section TargetEndpoints.
Variables pfalse ptrue : rat.
Variables (pfpos : 0 < pfalse) (ptpos : 0 < ptrue).
Hypothesis pnorm : pfalse + ptrue = 1.
Variables (pc : phase) (counts : counters) (script : script_state).
Local Notation "'Run' sampler" :=
  (run_exception
    (run_state
      (PTree.interp_tree device_handler
        (run_state (controller (embed sampler) pc) counts)) script))
  (at level 10, sampler at next level).

Example full_program_target_zero :
  Run (BoundedVonNeumann.factory (ltW pfpos) (ltW ptpos) pnorm 0) ≈ₚ
  Run (direct_q (lexx (0 : rat)) (ler01 : (0 : rat) <= 1)).
Proof. apply factory_controller_program_rewrite. Qed.

Example full_program_target_one :
  Run (BoundedVonNeumann.factory (ltW pfpos) (ltW ptpos) pnorm 1) ≈ₚ
  Run (direct_q (ler01 : (0 : rat) <= 1) (lexx (1 : rat))).
Proof. apply factory_controller_program_rewrite. Qed.
End TargetEndpoints.

Example next_fast_after_state :
  Prₛ[ run_state (controller implementation_sampler (Manufacturing 17)) initial_counters |
    [@select_mode true] ] = 2/5.
Proof. apply factory_next_action_probability. Qed.
Example next_safe_after_state :
  Prₛ[ run_state (controller implementation_sampler (Manufacturing 17)) initial_counters |
    [@select_mode false] ] = 3/5.
Proof. apply factory_next_action_probability. Qed.

Example pass_increments_and_ships j s :
  run_state (respond j Pass) s ≈ₚ
  Vis (Ship j) (λ _, Ret (count_pass s, (inl AwaitOrder : phase + Empty_set))).
Proof.
  expose_left. rewrite peutt_tau_l.
  expose_left. rewrite peutt_tau_l.
  expose_left. apply peutt_vis. intros [].
  apply PTree.Eq.Algebra.peutt_observe_eq. reflexivity.
Qed.
Example rework_retries_same_job j s :
  run_state (respond j Rework) s ≈ₚ Ret (count_rework s, (inl (Manufacturing j) : phase + Empty_set)).
Proof.
  expose_left. rewrite peutt_tau_l.
  expose_left. rewrite peutt_tau_l.
  apply PTree.Eq.Algebra.peutt_observe_eq. reflexivity.
Qed.
Example jam_requires_alarm_and_reset j s :
  run_state (respond j Jam) s ≈ₚ
  Vis (Alarm j) (λ _, Vis WaitReset (λ _, Ret (count_jam s, (inl (Manufacturing j) : phase + Empty_set)))).
Proof.
  expose_left. rewrite peutt_tau_l.
  expose_left. rewrite peutt_tau_l.
  expose_left. apply peutt_vis. intros [].
  expose_left. apply peutt_vis. intros [].
  apply PTree.Eq.Algebra.peutt_observe_eq. reflexivity.
Qed.

(** The source is not changed to terminate when the harness has no orders.
    The stop is an explicit exception in the DEVICE interpretation. *)
Example initial_offered_order : observe controller_impl =
  VisF (inr1 ReceiveOrder) (λ j,
    PTree.bind (Ret ((inl (Manufacturing j) : phase + Empty_set)))
      (λ v, match v with
       | inl pc => Tau (controller implementation_sampler pc)
       | inr r => Ret r
       end)).
Proof. reflexivity. Qed.
