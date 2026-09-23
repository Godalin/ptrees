(** Role: User-facing assembly or tree/backend adapter. Imports lower layers explicitly; not new semantic theory. *)
(** Convenience operations for the canonical finite subdistribution
    backend.  Raw [EnumQ] remains available for unnormalised finite weights;
    native probability programs should prefer [SubEnumQ]. *)
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
From PTree.Interp.Backend Require Import SubEnumQ.
From PTree.API Require Import Behavior BehaviorFreeOmega.

#[global] Polymorphic Instance SubEnumQ_CanonicalBehavior : CanonicalBehavior SubEnumQ :=
  @observable_free_omega_behavior SubEnumQ
    SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega.

Notation subenumQ_mdp_state_interp_atomic :=
  PTree.Interp.Backend.SubEnumQ.subenumQ_mdp_state_interp_atomic.

Set Implicit Arguments.
Set Contextual Implicit.

Definition submeas {E} {X} (mu : SubEnumQ X) : ptree E SubEnumQ X :=
  Prob mu (fun x : X => Ret x).

Definition subkernel {E} {X Y} (k : X -> SubEnumQ Y) :
    X -> ptree E SubEnumQ Y :=
  fun x => submeas (k x).

Variant subSampleE : Type -> Type :=
| SubSample {A : Type} : SubEnumQ A -> subSampleE A.

Definition handle_subsample {E} {R} (e : subSampleE R) :
    ptree E SubEnumQ R :=
  match e with
  | SubSample _ mu => submeas mu
  end.
