(** Phase 4b.2: exact preservation of the native zero-pruning operation.
    This is not a carrier migration or a new definition of coupling. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist FinitePruning.

Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.Backend.Common.RatSubTypes.nnQ.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.

From PTree.Prob.Backend.EnumQ Require Import Representation FrontierLift IndexedCoupling.
From PTree.Prob.Backend.Common Require Import RatSubTypes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ IndexedCoupling ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** The accepted recursion, kept only in this test, not as a runtime adapter. *)
Fixpoint reference_prune {A} (mu : EnumQ A) : EnumQ A :=
  match mu with
  | [] => []
  | (p,x)::tl => if p == RatSubTypes.nnQ_0 then reference_prune tl
                 else (p,x)::reference_prune tl
  end.

Example native_prune_exact {A} (mu : EnumQ A) : enumQ_prune mu = reference_prune mu.
Proof. reflexivity. Qed.

Example native_prune_uses_shared {A} (mu : EnumQ A) :
  enumQ_prune mu = finite_prune (fun p => p == RatSubTypes.nnQ_0) mu.
Proof. reflexivity. Qed.

Example native_equality_unchanged {A} (mu nu : EnumQ A) :
  enumQ_meas_eq mu nu <-> indexed_coupling eq (reference_prune mu) (reference_prune nu).
Proof. reflexivity. Qed.

Example rational_scalar_prune_commutes {A} (mu : EnumQ A) :
  finite_prune (fun p : rat => p == 0)
    (List.map (fun px => (RatSubTypes.Qval (fst px), snd px)) mu) =
  List.map (fun px => (RatSubTypes.Qval (fst px), snd px)) (enumQ_prune mu).
Proof.
  apply finite_prune_map_weights=> p.
  apply/idP/idP.
  - move/eqP=> Hp. apply/eqP; apply val_inj; exact Hp.
  - move/eqP=> ->; reflexivity.
Qed.

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
  List.In (p,x) (enumQ_prune mu) <->
  List.In (p,x) mu /\ p <> RatSubTypes.nnQ_0.
Proof.
  split; first exact: enumQ_prune_in_source.
  intros [Hin Hnz]; apply finite_prune_in; split; first exact Hin.
  apply/eqP=> Hp; exact (Hnz Hp).
Qed.

Section SharedRecords.
Variable R : numDomainType.
Example checked_prune_mass {A} (mu : FiniteSubdist R A) :
  finite_subdist_expect (finite_subdist_prune (fun p => p == 0) mu) (fun _ => 1) =
  finite_subdist_expect mu (fun _ => 1).
Proof. exact: finite_subdist_prune_zero_expect. Qed.
Example checked_prune_bound {A} d (mu : FiniteSubdist R A) :
  finite_mass (finite_subdist_enum (finite_subdist_prune d mu)) <= 1.
Proof. exact: finite_subdist_mass_bound. Qed.
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
