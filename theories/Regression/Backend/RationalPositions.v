(** Native checked rational positions retain the accepted raw-list recursion.
    Historical scalar conversion checks are regression-only, not backend adapters. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist FinitePositions.

Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.

From PTree.Prob.Backend.EnumQ Require Import Representation IndexedCoupling.
From PTree.Prob.Legacy Require Import RatSubTypes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ IndexedCoupling ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Notation Q := rat_rat__canonical__Num_NumDomain.

(** Exact copies of the two accepted native recursions; not a backend adapter. *)
Fixpoint reference_index {A} (n : nat) (mu : list (rat*A)) : list (rat*nat) :=
  match mu with [] => [] | (p,_)::tl => (p,n)::reference_index (S n) tl end.
Fixpoint reference_value_index {A} (n : nat) (mu : list (rat*A)) : list (rat*(A*nat)) :=
  match mu with [] => [] | (p,x)::tl => (p,(x,n))::reference_value_index (S n) tl end.

Example native_index_exact {A} n (mu : EnumQ A) : enumQ_raw (index_from n mu) = reference_index n (enumQ_raw mu).
Proof. reflexivity. Qed.
Example native_value_index_exact {A} n (mu : EnumQ A) :
  enumQ_raw (value_index_joint_from n mu) = reference_value_index n (enumQ_raw mu).
Proof. reflexivity. Qed.

Example native_index_uses_shared {A} n (mu : EnumQ A) :
  enumQ_raw (index_from n mu) = finite_index_from n (enumQ_raw mu).
Proof. reflexivity. Qed.
Example native_value_index_uses_shared {A} n (mu : EnumQ A) :
  enumQ_raw (value_index_joint_from n mu) = finite_value_index_from n (enumQ_raw mu).
Proof. reflexivity. Qed.

Example rational_scalar_index_commutes {A} n (mu : list (RatSubTypes.nnQ*A)) :
  finite_index_from n (List.map (fun px => (RatSubTypes.Qval (fst px), snd px)) mu) =
  List.map (fun pi => (RatSubTypes.Qval (fst pi), snd pi)) (finite_index_from n mu).
Proof. exact: finite_index_map_weights. Qed.

Example rational_scalar_joint_commutes {A} n (mu : list (RatSubTypes.nnQ*A)) :
  finite_value_index_from n (List.map (fun px => (RatSubTypes.Qval (fst px), snd px)) mu) =
  List.map (fun pxi => (RatSubTypes.Qval (fst pxi), snd pxi)) (finite_value_index_from n mu).
Proof. exact: finite_value_index_map_weights. Qed.

Example rational_checked_index_commutes {A} n (mu : list (RatSubTypes.nnQ*A))
    (Hnn : @finite_nonnegative Q A (List.map (fun px => (RatSubTypes.Qval (fst px), snd px)) mu)) :
  finite_enum_raw (finite_enum_index_from n (finite_enum_of_list Hnn)) =
  List.map (fun pi => (RatSubTypes.Qval (fst pi), snd pi)) (finite_index_from n mu).
Proof. exact: finite_index_map_weights. Qed.

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

Section GenericShared.
Variable R : numDomainType.
Example indexed_subdistribution_mass {A} n (mu : FiniteSubdist R A) :
  finite_mass (finite_subdist_enum (finite_subdist_index_from n mu)) =
  finite_mass (finite_subdist_enum mu).
Proof. exact: finite_enum_index_mass. Qed.
Example indexed_subdistribution_bound {A} n (mu : FiniteSubdist R A) :
  finite_mass (finite_subdist_enum (finite_subdist_index_from n mu)) <= 1.
Proof. exact: finite_subdist_mass_bound. Qed.
Example joint_subdistribution_mass {A} n (mu : FiniteSubdist R A) :
  finite_mass (finite_subdist_enum (finite_subdist_value_index_from n mu)) =
  finite_mass (finite_subdist_enum mu).
Proof. exact: finite_enum_value_index_mass. Qed.
Example joint_left_marginal {A} n (mu : FiniteSubdist R A) (f : A -> R) :
  finite_subdist_expect (finite_subdist_value_index_from n mu) (fun xi => f (fst xi)) =
  finite_subdist_expect mu f.
Proof. exact: finite_value_index_expect. Qed.
Example joint_right_marginal {A} n (mu : FiniteSubdist R A) :
  List.map (fun pxi => (fst pxi, snd (snd pxi)))
    (finite_enum_raw (finite_subdist_enum (finite_subdist_value_index_from n mu))) =
  finite_enum_raw (finite_subdist_enum (finite_subdist_index_from n mu)).
Proof. exact: finite_value_index_snd. Qed.
End GenericShared.

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
