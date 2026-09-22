(** Final carrier contract: ordinary scalar storage, exact list structure,
    shared operations and Q-to-R transport, without a legacy conversion layer. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import
  FiniteEnum FiniteSubdist FiniteScalarMap FinitePruning.
From PTree.Prob.Backend.EnumQ Require Import Representation FrontierLift.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumR Require Import Representation RationalEmbedding.

Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
Fail Check PTree.Prob.Legacy.RationalDiscrete.DiscreteInterface.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Core.PTreeDefinition.ptree.

Set Implicit Arguments.
Unset Strict Implicit.
Import EnumQ GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Example rational_weighting_is_shared A :
  EnumQ A = FiniteEnum rat_rat__canonical__Num_NumDomain A.
Proof. reflexivity. Qed.
Example rational_subdistribution_is_shared A :
  SubEnumQ A = FiniteSubdist rat_rat__canonical__Num_NumDomain A.
Proof. reflexivity. Qed.
Example real_subdistribution_is_shared (R : realType) A :
  SubEnumR R A = FiniteSubdist R A.
Proof. reflexivity. Qed.

Example rational_bind_is_shared {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  bind_EnumQ mu k = finite_enum_bind mu k.
Proof. reflexivity. Qed.
Example rational_subbind_is_shared {A B} (mu : SubEnumQ A) (k : A -> SubEnumQ B) :
  subenumQ_bind mu k = finite_subdist_bind mu k.
Proof. reflexivity. Qed.

Definition zero_duplicate : SubEnumQ bool.
Proof.
  refine (subenumQ_of_list (mu := [(0,false); (1/4,true); (1/2,false); (1/4,true)]) _ _).
  - intros p x [H|[H|[H|[H|[]]]]]; inversion H; subst; vm_compute; reflexivity.
  - vm_compute; reflexivity.
Defined.

Example entries_preserve_order_and_duplicates :
  subenumQ_data zero_duplicate = [(0,false); (1/4,true); (1/2,false); (1/4,true)].
Proof. reflexivity. Qed.
Example pruning_only_removes_zero :
  enumQ_raw (enumQ_prune (subenumQ_raw zero_duplicate)) =
    [(1/4,true); (1/2,false); (1/4,true)].
Proof. vm_compute; reflexivity. Qed.
Example signed_test_is_preserved :
  enumQ_expect (fun b => if b then -3 else 1) (subenumQ_raw zero_duplicate) = -1.
Proof. vm_compute; reflexivity. Qed.

Example rational_to_real_uses_shared_transport (R : realType) {A} (mu : SubEnumQ A) :
  subenumQ_to_R R mu = finite_subdist_map_weights (@rational_scalar_monotone R) mu.
Proof. reflexivity. Qed.

Section LargeCarrier.
Universe u.
Variable A : Type@{u}.
Example high_carrier_native : SubEnumQ Type@{u} := subenumQ_ret A.
Example high_carrier_bridge (R : realType) : SubEnumR R Type@{u} :=
  subenumQ_to_R R high_carrier_native.
End LargeCarrier.
