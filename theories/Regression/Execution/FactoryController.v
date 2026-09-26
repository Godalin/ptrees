(** A single vertical-slice regression: independent device replies, State,
    exact visible probabilities and the same extracted infinite program. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import EnumQ ProbabilisticTraceEnumQ.
From PTree.Interp Require Import State.
From PTree.Examples.FactoryController Require Import Controller Facts Observation Probability Scripted.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Set Default Timeout 20.

(** Expose only the next operational node, then use the public Tau/Vis laws. *)
Ltac expose_left :=
  lazymatch goal with
  | |- ?R ?t ?v =>
    let u := eval cbn in (go (observe t)) in
    transitivity u; [apply PTree.Eq.Algebra.peutt_observe_eq; reflexivity|]
  end.

Example infinite_source_refinement : controller_impl ≈ₚ controller_spec.
Proof. apply controller_refinement. Qed.
Example interpreted_refinement : demo_impl ≈ₚ demo_spec.
Proof. apply scripted_controller_refinement. Qed.
Example raw_factory_nodes_are_probabilities : probabilistic_ptree controller_impl.
Proof. apply implementation_probability. Qed.

Example next_fast_after_state :
  Prₜ[ run_state (controller implementation_sampler (Manufacturing 17)) initial_counters |
    [@select_mode true] ] = 2/5.
Proof. apply factory_next_action_probability. Qed.
Example next_safe_after_state :
  Prₜ[ run_state (controller implementation_sampler (Manufacturing 17)) initial_counters |
    [@select_mode false] ] = 3/5.
Proof. apply factory_next_action_probability. Qed.

Example pass_increments_and_ships j s :
  run_state (respond j Pass) s ≈ₚ
  Vis (Ship j) (fun _ => Ret (count_pass s, (inl AwaitOrder : phase + Empty_set))).
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
  Vis (Alarm j) (fun _ => Vis WaitReset (fun _ => Ret (count_jam s, (inl (Manufacturing j) : phase + Empty_set)))).
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
  VisF (inr1 ReceiveOrder) (fun j =>
    PTree.bind (Ret ((inl (Manufacturing j) : phase + Empty_set)))
      (fun v => match v with
       | inl pc => Tau (controller implementation_sampler pc)
       | inr r => Ret r
       end)).
Proof. reflexivity. Qed.
