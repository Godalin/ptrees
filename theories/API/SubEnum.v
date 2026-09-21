(** Role: User-facing assembly or tree/backend adapter. Imports lower layers explicitly; not new semantic theory. *)
(** Convenience operations for the canonical finite subdistribution
    backend.  Raw [Enum] remains available for unnormalised finite weights;
    native probability programs should prefer [SubEnum]. *)
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.SubEnum.Measure.
From PTree.Interp.Backend Require Import SubEnum.

Notation subenum_mdp_state_interp_atomic :=
  PTree.Interp.Backend.SubEnum.subenum_mdp_state_interp_atomic.

Set Implicit Arguments.
Set Contextual Implicit.

Definition submeas {E} {X} (mu : SubEnum X) : ptree E SubEnum X :=
  Prob mu (fun x : X => Ret x).

Definition subkernel {E} {X Y} (k : X -> SubEnum Y) :
    X -> ptree E SubEnum Y :=
  fun x => submeas (k x).

Variant subSampleE : Type -> Type :=
| SubSample {A : Type} : SubEnum A -> subSampleE A.

Definition handle_subsample {E} {R} (e : subSampleE R) :
    ptree E SubEnum R :=
  match e with
  | SubSample _ mu => submeas mu
  end.
