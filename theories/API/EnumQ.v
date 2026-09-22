(** Role: User-facing assembly or tree/backend adapter. Imports lower layers explicitly; not new semantic theory. *)
(** EnumQ-specific convenience operations for probability trees.

    They used to live in [PTreeDefinition], forcing every generic tree and
    measure development to load the legacy finite-distribution backend. *)
From mathcomp Require Import eqtype.
From ExtLib.Structures Require Import Monads.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation.

Set Implicit Arguments.
Set Contextual Implicit.

Import EnumQ.

Definition meas {E} {X : eqType} (mu : EnumQ X) : ptree E EnumQ X :=
  Prob mu ret.

Definition kernel {E} {X Y : eqType} (k : X -> EnumQ Y) :
    X -> ptree E EnumQ Y :=
  fun x => meas (k x).

Variant sampleE : eqType -> Type :=
| Sample {A : eqType} : EnumQ A -> sampleE A.

Definition handle_sample {E} {R : eqType} (e : sampleE R) :
    ptree E EnumQ R :=
  match e with
  | Sample _ mu => meas mu
  end.
