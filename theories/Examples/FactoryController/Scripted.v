(** A finite experiment around the SAME infinite controller. Exhausting a
    device script raises an explicit experiment-stop exception, not Lost or
    program termination. Internal samplers still have no retry bound. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From ITree.Events Require Import State Exception.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Interp Require Import State Exception.
From PTree.Examples.FactoryController Require Import Controller.
Import ListNotations EnumQ.
Set Implicit Arguments.
Unset Strict Implicit.

Inductive log_entry :=
| Accepted (job : nat)
| Attempted (job : nat) (fast : bool) (reply : machine_reply)
| Shipped (job : nat)
| Alarmed (job : nat)
| ResetAcknowledged.
Record script_state := Script {
  orders : list nat;
  replies : list machine_reply;
  reverse_log : list log_entry
}.
Definition scriptE := sum1 (stateE script_state) (sum1 (exceptE script_state) void1).
Definition script_tree := ptree scriptE EnumQ.

Definition stop_experiment {A} (s : script_state) : script_tree A := Exception.throw s.
Definition remember {A} (s : script_state) (v : A) : script_tree A :=
  PTree.bind (State.put s) (fun _ => Ret v).

Definition device_handler X (e : deviceE X) : script_tree X :=
  PTree.bind State.get (fun s =>
  match e in deviceE Y return script_tree Y with
  | ReceiveOrder => match orders s with
      | [] => stop_experiment s
      | j :: rest => remember (Script rest (replies s) (Accepted j :: reverse_log s)) j
      end
  | RunMachine j fast => match replies s with
      | [] => stop_experiment s
      | reply :: rest => remember
          (Script (orders s) rest (Attempted j fast reply :: reverse_log s)) reply
      end
  | Ship j => remember (Script (orders s) (replies s) (Shipped j :: reverse_log s)) tt
  | Alarm j => remember (Script (orders s) (replies s) (Alarmed j :: reverse_log s)) tt
  | WaitReset => remember (Script (orders s) (replies s) (ResetAcknowledged :: reverse_log s)) tt
  end).

Definition close_controller (t : ptree deviceE EnumQ (counters * Empty_set)) s :=
  run_exception (run_state (PTree.interp device_handler t) s).
Definition scripted_impl counts s := close_controller (device_controller_impl counts) s.
Definition scripted_spec counts s := close_controller (device_controller_spec counts) s.
Definition demo_script := Script [17;23] [Rework;Jam;Pass;Pass] [].
Definition demo_impl := scripted_impl initial_counters demo_script.
Definition demo_spec := scripted_spec initial_counters demo_script.

Definition chronological_log s := rev (reverse_log s).
