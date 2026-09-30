(** Role: finite probability/coupling/backend example. *)
(** Current finite-list contracts: positions, pruning, exact operations,
    scalar transport and shared carriers. No historical nnQ conversion layer. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist
  FinitePositions FinitePresentation FinitePruning FiniteListAlgebra FiniteAtoms FiniteScalarMap.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Core.PTreeDefinition.ptree.

From Coq Require List.
From mathcomp Require ssreflect ssrbool eqtype ssralg ssrnum order rat.
Require PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FinitePositions.
Require PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.IndexedCoupling.
Module RationalPositions.
(** Native checked rational positions retain the shared raw-list recursion;
    positions include duplicate values and zero-weight entries. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import List.
Import ssreflect ssrbool eqtype ssralg ssrnum order rat.
Import PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FinitePositions.

Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.IndexedCoupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ IndexedCoupling ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Notation Q := rat_rat__canonical__Num_NumDomain.

Example native_index_uses_shared {A} n (mu : EnumQ A) :
  enumQ_raw (index_from n mu) = finite_index_from n (enumQ_raw mu).
Proof. reflexivity. Qed.
Example native_value_index_uses_shared {A} n (mu : EnumQ A) :
  enumQ_raw (value_index_joint_from n mu) = finite_value_index_from n (enumQ_raw mu).
Proof. reflexivity. Qed.

(** Positions are never merged or pruned: duplicates and zero weights still
    occupy their exact slots. The existing native zero-pruning operation is
    separate and unchanged. *)
Example positions_retain_zero_and_duplicates :
  @finite_value_index_from rat bool 7 [(1,true); (0,false); (1,true)] =
  [(1,(true,7)); (0,(false,8)); (1,(true,9))].
Proof. reflexivity. Qed.
Example empty_positions : @finite_index_from rat Empty_set 7 [] = [].
Proof. reflexivity. Qed.
Example out_of_range_has_no_slot {W A} n (mu : list (W * A)) i :
  nth_error mu i = None -> nth_error (finite_index_from n mu) i = None.
Proof. intro H; by rewrite finite_index_nth H. Qed.

Section LargeCarrier.
Universe u.
Variable R : numDomainType.
Example large_carrier_index (X : Type@{u}) :
  finite_enum_raw (finite_enum_index_from 9 (finite_enum_ret R X)) = [(1,9)].
Proof. reflexivity. Qed.
Example large_carrier_joint (X : Type@{u}) :
  finite_enum_raw (finite_enum_value_index_from 9 (finite_enum_ret R X)) = [(1,(X,9))].
Proof. reflexivity. Qed.
End LargeCarrier.

End RationalPositions.

From Coq Require List.
From mathcomp Require ssreflect ssrbool ssrfun eqtype ssrnat seq fintype tuple ssralg ssrnum order rat.
Require PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FinitePresentation.
Require PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.FiniteTransport PTree.Prob.Backend.EnumQ.FinitePresentation.
Require PTree.Prob.Backend.SubEnumQ.Measure.
Module RationalPresentation.
(** Shared checked rational presentations preserve raw slots and decoding. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import List.
Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype tuple ssralg ssrnum order rat.
Import PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FinitePresentation.

Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.FiniteTransport PTree.Prob.Backend.EnumQ.FinitePresentation.
Import PTree.Prob.Backend.SubEnumQ.Measure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Example native_positions_use_shared {A} (mu : EnumQ A) : enumQ_raw (enumQ_positions mu) = finite_positions (enumQ_raw mu).
Proof. reflexivity. Qed.

(** Raw and checked positions decode to the same list, without a scalar
    conversion or a change in order, multiplicity or zero entries. *)
Example rational_decoded_presentation {A} (mu : EnumQ A) :
  let raw := enumQ_raw mu in
  [seq (px.1, finite_position_value raw px.2) | px <- finite_positions raw] =
  enumQ_raw (emap (enumQ_position_value mu) (enumQ_positions mu)).
Proof. cbn zeta; by rewrite finite_positions_decode enumQ_positions_decode. Qed.

Definition duplicate_zero_list : list (rat * bool) := [:: (0,false); (1,true); (2,true); (0,true)].
Example presentation_retains_every_slot : size (finite_positions duplicate_zero_list) = 4%nat.
Proof. by rewrite finite_positions_size. Qed.
Example presentation_indices_not_values :
  [seq val px.2 | px <- finite_positions duplicate_zero_list] = [:: 0%nat; 1%nat; 2%nat; 3%nat].
Proof. by rewrite /finite_positions -map_comp /= val_enum_ord. Qed.
Example presentation_duplicate_zero_roundtrip :
  [seq (px.1, finite_position_value duplicate_zero_list px.2) | px <- finite_positions duplicate_zero_list] =
  duplicate_zero_list.
Proof. exact: finite_positions_decode. Qed.
Example presentation_does_not_require_inhabitant :
  @finite_positions rat Empty_set [::] = [::].
Proof. apply size0nil; by rewrite finite_positions_size. Qed.
Example signed_observable_preserved (f : bool -> rat) :
  finite_expect (fun i => f (finite_position_value duplicate_zero_list i))
    (finite_positions duplicate_zero_list) = finite_expect f duplicate_zero_list.
Proof. exact: finite_positions_expect. Qed.

Section SharedRecords.
Variable R : numDomainType.
Example shared_function_carrier (f : nat -> nat) :
  finite_enum_raw (finite_enum_map (finite_position_value (finite_enum_raw (finite_enum_ret R f)))
    (finite_enum_positions (finite_enum_ret R f))) = [:: (1,f)].
Proof. exact: finite_enum_positions_decode. Qed.
End SharedRecords.

Section LargeCarrier.
Universe u.
Variable R : numDomainType.
Example large_carrier_presentation (X : Type@{u}) :
  finite_enum_raw (finite_enum_map (finite_position_value (finite_enum_raw (finite_enum_ret R X)))
    (finite_enum_positions (finite_enum_ret R X))) = [:: (1,X)].
Proof. exact: finite_enum_positions_decode. Qed.
End LargeCarrier.

End RationalPresentation.

From Coq Require List.
From mathcomp Require ssreflect ssrbool eqtype ssralg ssrnum order rat.
Require PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FinitePruning.
Require PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.IndexedCoupling.
Module RationalPruning.
(** Checked rational pruning preserves the accepted raw-list operation.
    Equality/lifting still uses indexed coupling after zero-pruning. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import List.
Import ssreflect ssrbool eqtype ssralg ssrnum order rat.
Import PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FinitePruning.

Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.IndexedCoupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ IndexedCoupling ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Example native_prune_uses_shared {A} (mu : EnumQ A) :
  enumQ_raw (enumQ_prune mu) = finite_prune (fun p => p == 0) (enumQ_raw mu).
Proof. reflexivity. Qed.

Example native_equality_unchanged {A} (mu nu : EnumQ A) :
  enumQ_meas_eq mu nu <-> indexed_coupling eq
    (finite_enum_prune (fun p => p == 0) mu) (finite_enum_prune (fun p => p == 0) nu).
Proof. reflexivity. Qed.

Example zero_pruning_preserves_order_and_duplicates :
  finite_prune (fun p : rat => p == 0)
    [(0,false); (1,true); (2,false); (0,true); (1,true)] =
  [(1,true); (2,false); (1,true)].
Proof. reflexivity. Qed.

Example pruning_does_not_renormalize :
  finite_expect (fun _ : bool => (1 : rat))
    (finite_prune (fun p : rat => p == 0) [(0,false); ((1/2)%R,true)]) = 1/2.
Proof. change ((1/2 : rat) * 1 + 0 = 1/2); by rewrite mulr1 addr0. Qed.

Example all_zero_prunes_to_empty :
  finite_prune (fun p : rat => p == 0) [(0,true); (0,false)] = [].
Proof. reflexivity. Qed.

Example empty_carrier_prune : @finite_prune rat (fun p => p == 0) Empty_set [] = [].
Proof. reflexivity. Qed.

Example duplicate_signed_observation_preserved (f : bool -> rat) :
  finite_expect f (finite_prune (fun p : rat => p == 0) [(1,true); (0,false); (2,true)]) =
  finite_expect f [(1,true); (0,false); (2,true)].
Proof. exact: finite_expect_prune_zero. Qed.

Example retained_native_support {A} (mu : EnumQ A) p (x : A) :
  List.In (p,x) (enumQ_raw (enumQ_prune mu)) <->
  List.In (p,x) (enumQ_raw mu) /\ p <> 0.
Proof.
  split; first exact: enumQ_prune_in_source.
  intros [Hin Hnz]; apply finite_prune_in; split; first exact Hin.
  apply/eqP=> Hp; exact (Hnz Hp).
Qed.

Section SharedRecords.
Variable R : numDomainType.
Example general_discard_can_lose_mass {A} (mu : FiniteEnum R A) :
  finite_mass (finite_enum_prune (fun _ => true) mu) = 0.
Proof.
  destruct mu as [raw Hnn]; cbn; clear Hnn.
  induction raw as [|[p x] tl IH]; cbn; [reflexivity|exact IH].
Qed.
End SharedRecords.

Section LargeCarrier.
Universe u.
Variable R : numDomainType.
Example large_carrier_prune (X : Type@{u}) :
  finite_enum_raw (finite_enum_prune (fun p => p == 0) (finite_enum_ret R X)) = [(1,X)].
Proof. cbn; by rewrite oner_eq0. Qed.
End LargeCarrier.

End RationalPruning.

From Coq Require List.
From mathcomp Require ssreflect ssrbool ssrfun eqtype seq fintype bigop ssralg ssrnum order rat reals.
Require PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FiniteListAlgebra PTree.Prob.Backend.Common.FiniteAtoms PTree.Prob.Backend.Common.FiniteScalarMap.
Require PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.FinitePresentation.
Module RationalFiniteAlgebra.
(** Concrete list algebra and scalar transport; no historical recursion copies. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import List.
Import ssreflect ssrbool ssrfun eqtype seq fintype bigop ssralg ssrnum order rat reals.
Import PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FiniteListAlgebra PTree.Prob.Backend.Common.FiniteAtoms PTree.Prob.Backend.Common.FiniteScalarMap.
Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.FinitePresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Example bind_keeps_zero_blocks_and_duplicates :
  finite_bind_with (fun p q : rat => p*q) [:: (0,false); (1,true); (1,true)]
    (fun b => [:: (2,b); (0,b)]) =
  [:: (0,false); (0,false); (2,true); (0,true); (2,true); (0,true)].
Proof. reflexivity. Qed.
Example duplicate_atom_mass :
  finite_atom true [:: ((1:rat),true); (0,true); (2,false); (3,true)] = 4.
Proof. by vm_compute. Qed.
Example atom_observations_agree {A : finType} (mu : EnumQ A) f :
  enumQ_expect f mu = \sum_x finite_atom x (enumQ_raw mu) * f x.
Proof. by rewrite enumQ_expect_finite finite_expect_by_atoms. Qed.

Section ScalarTransport.
Variable R : realType.
Local Definition rat_to_real : {rmorphism rat -> R} := [the {rmorphism rat -> R} of ratr].
Local Lemma rat_to_real_mono : forall x y, x <= y -> rat_to_real x <= rat_to_real y.
Proof. move=> x y H; by rewrite /rat_to_real /= ler_rat. Qed.

Example ordinary_q_to_r_mass {A} (mu : FiniteSubdist rat_rat__canonical__Num_NumDomain A) :
  finite_subdist_expect (finite_subdist_map_weights rat_to_real_mono mu) (fun _ => 1) =
  ratr (finite_subdist_expect mu (fun _ => 1)).
Proof. exact: finite_map_weights_mass. Qed.
Example ordinary_q_to_r_bind {A B} (mu : FiniteSubdist rat_rat__canonical__Num_NumDomain A)
    (k : A -> FiniteSubdist rat_rat__canonical__Num_NumDomain B) :
  finite_enum_raw (finite_subdist_enum (finite_subdist_map_weights rat_to_real_mono (finite_subdist_bind mu k))) =
  finite_enum_raw (finite_subdist_enum (finite_subdist_bind
    (finite_subdist_map_weights rat_to_real_mono mu) (fun x => finite_subdist_map_weights rat_to_real_mono (k x)))).
Proof. exact: finite_subdist_map_weights_bind. Qed.
End ScalarTransport.

End RationalFiniteAlgebra.

From Coq Require List.
From mathcomp Require ssreflect ssrbool ssralg ssrnum order rat reals.
Require PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FiniteScalarMap PTree.Prob.Backend.Common.FinitePruning.
Require PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift.
Require PTree.Prob.Backend.SubEnumQ.Representation.
Require PTree.Prob.Backend.SubEnumR.Representation PTree.Prob.Backend.SubEnumR.RationalEmbedding.
Module FiniteBackendConsolidation.
(** Final carrier contract: ordinary scalar storage, exact list structure,
    shared operations and Q-to-R transport, without a legacy conversion layer. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import List.
Import ssreflect ssrbool ssralg ssrnum order rat reals.
Import PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.Common.FiniteSubdist PTree.Prob.Backend.Common.FiniteScalarMap PTree.Prob.Backend.Common.FinitePruning.
Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.FrontierLift.
Import PTree.Prob.Backend.SubEnumQ.Representation.
Import PTree.Prob.Backend.SubEnumR.Representation PTree.Prob.Backend.SubEnumR.RationalEmbedding.

Fail Check PTree.Prob.Legacy.RationalDiscrete.DiscreteInterface.

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

End FiniteBackendConsolidation.
