(** Interactive factory: the existing nested sampler, not a new algorithm.
    Three independent sources of unbounded behavior: VN, binary factory,
    and the reactive service (including environment-driven retries). *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From mathcomp Require Import ssreflect ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Interp Require Import State.
From PTree.Examples.BernoulliFactory Require Import BernoulliFactory.
Set Implicit Arguments.
Unset Strict Implicit.
Import EnumQ.

Inductive machine_reply := Pass | Rework | Jam.
Variant deviceE : Type -> Type :=
| ReceiveOrder : deviceE nat
| RunMachine (job : nat) (fast : bool) : deviceE machine_reply
| Ship (job : nat) : deviceE unit
| Alarm (job : nat) : deviceE unit
| WaitReset : deviceE unit.

Record counters := Counters { completed : nat; retries : nat; jams : nat }.
Definition initial_counters := Counters 0 0 0.
Definition count_pass s := Counters (S (completed s)) (retries s) (jams s).
Definition count_rework s := Counters (completed s) (S (retries s)) (jams s).
Definition count_jam s := Counters (completed s) (retries s) (S (jams s)).
Definition controllerE := sum1 (stateE counters) deviceE.
Definition tree := ptree controllerE EnumQ.
Inductive phase := AwaitOrder | Manufacturing (job : nat).

Definition emit {X} (e : deviceE X) : tree X := PTree.trigger (inr1 e).
Definition update (f : counters -> counters) : tree unit :=
  PTree.bind (State.get) (fun s => State.put (f s)).

Definition respond (job : nat) (reply : machine_reply) : tree (phase + Empty_set) :=
  match reply with
  | Pass => PTree.bind (update count_pass) (fun _ =>
      PTree.bind (emit (Ship job)) (fun _ => Ret (inl AwaitOrder)))
  | Rework => PTree.bind (update count_rework) (fun _ => Ret (inl (Manufacturing job)))
  | Jam => PTree.bind (update count_jam) (fun _ =>
      PTree.bind (emit (Alarm job)) (fun _ =>
      PTree.bind (emit WaitReset) (fun _ => Ret (inl (Manufacturing job)))))
  end.

Definition attempt (sampler : tree bool) job : tree (phase + Empty_set) :=
  PTree.bind sampler (fun fast =>
    Vis (inr1 (RunMachine job fast)) (respond job)).
Definition controller_step sampler (pc : phase) : tree (phase + Empty_set) :=
  match pc with
  | AwaitOrder => Vis (inr1 ReceiveOrder) (fun job => Ret (inl (Manufacturing job)))
  | Manufacturing job => attempt sampler job
  end.
Definition controller sampler pc : tree Empty_set := PTree.iter (controller_step sampler) pc.

(** Closed source sampler is embedded by the ordinary interpreter. *)
Definition embed {E A} (t : ptree factoryE EnumQ A) : ptree E EnumQ A :=
  PTree.interp (fun X (e : factoryE X) => match e with end) t.
Definition implementation_sampler : tree bool := embed third_to_two_fifths.
Definition specification_sampler : tree bool := embed direct_two_fifths.
Definition controller_impl := controller implementation_sampler AwaitOrder.
Definition controller_spec := controller specification_sampler AwaitOrder.
Definition device_controller_impl s := run_state controller_impl s.
Definition device_controller_spec s := run_state controller_spec s.
