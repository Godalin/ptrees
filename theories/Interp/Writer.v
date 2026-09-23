(** Standard ITree Writer, implemented as a thin State client. Output order
    is [monoid_plus old new]; probability remains a native PTree node. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monoid.
From ITree.Events Require Import Writer State.
From ITree.Core Require Import Subevent.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Interp Require Import State.
Set Implicit Arguments.
Unset Strict Implicit.

Definition tell {W E MN} `{writerE W -< E} (w : W) : ptree E MN unit :=
  PTree.trigger (subevent unit (Tell w)).

Definition writer_handler {W E MN} (op : Monoid W) X (e : (writerE W +' E) X) :
    ptree (stateE W +' E) MN X :=
  match e with
  | inl1 we => match we in writerE _ X return ptree (stateE W +' E) MN X with
      | Tell w => Vis (inl1 (Get W)) (fun log =>
          Vis (inl1 (Put W (monoid_plus op log w))) (fun _ => Ret tt)) end
  | inr1 fe => Vis (inr1 fe) (fun x => Ret x)
  end.

Definition run_writer {W E MN A} (op : Monoid W) (t : ptree (writerE W +' E) MN A) :
    ptree E MN (W*A) :=
  run_state (PTree.interp (writer_handler op) t) (monoid_unit op).

Lemma writer_tell_appends {W E MN} (op : Monoid W) w :
  @writer_handler W E MN op _ (inl1 (Tell w)) =
    Vis (inl1 (Get W)) (fun log =>
      Vis (inl1 (Put W (monoid_plus op log w))) (fun _ => Ret tt)).
Proof. reflexivity. Qed.
