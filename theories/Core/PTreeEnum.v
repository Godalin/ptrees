(** Enum-specific convenience operations for probability trees.

    They used to live in [PTreeDefinition], forcing every generic tree and
    measure development to load the legacy finite-distribution backend. *)
From mathcomp Require Import eqtype.
From ExtLib Require Import Structures.Monads.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import DiscreteMC.

Set Implicit Arguments.
Set Contextual Implicit.

Import Enum.

Definition meas {E} {X : eqType} (mu : Enum X) : ptree E Enum X :=
  Prob mu ret.

Definition kernel {E} {X Y : eqType} (k : X -> Enum Y) :
    X -> ptree E Enum Y :=
  fun x => meas (k x).

Variant sampleE : eqType -> Type :=
| Sample {A : eqType} : Enum A -> sampleE A.

Definition handle_sample {E} {R : eqType} (e : sampleE R) :
    ptree E Enum R :=
  match e with
  | Sample _ mu => meas mu
  end.
