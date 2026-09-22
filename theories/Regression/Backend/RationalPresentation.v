(** Shared checked rational presentations preserve raw slots and decoding. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype tuple ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist FinitePresentation.

Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.

From PTree.Prob.Backend.EnumQ Require Import Representation Map FiniteTransport FinitePresentation.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition reference_position {A} (mu : EnumQ A) := 'I_(size (enumQ_raw mu)).
Definition reference_entry {A} (mu : EnumQ A) (i : reference_position mu) := tnth (in_tuple (enumQ_raw mu)) i.
Arguments reference_entry {A} mu i.
Definition reference_positions {A} (mu : EnumQ A) : list (rat * reference_position mu) :=
  [seq ((reference_entry mu i).1, i) | i <- enum (reference_position mu)].

Example native_position_exact {A} (mu : EnumQ A) : enumQ_position mu = reference_position mu.
Proof. reflexivity. Qed.
Example native_entry_exact {A} (mu : EnumQ A) i : enumQ_position_entry mu i = reference_entry mu i.
Proof. reflexivity. Qed.
Example native_positions_exact {A} (mu : EnumQ A) : enumQ_raw (enumQ_positions mu) = reference_positions mu.
Proof. reflexivity. Qed.
Example native_positions_use_shared {A} (mu : EnumQ A) : enumQ_raw (enumQ_positions mu) = finite_positions (enumQ_raw mu).
Proof. reflexivity. Qed.
Example native_decode_exact {A} (mu : EnumQ A) :
  enumQ_raw (emap (fun i => (reference_entry mu i).2) (enumQ_positions mu)) = enumQ_raw mu.
Proof. exact: enumQ_positions_decode. Qed.
Example native_subdistribution_raw_exact {A} (mu : SubEnumQ A) :
  enumQ_raw (subenumQ_raw (subenumQ_positions mu)) = reference_positions (subenumQ_raw mu).
Proof. reflexivity. Qed.

(** The old/new scalar layers decode to the same coefficient-mapped list;
    this is not a runtime conversion layer, nor a new scalar transport API. *)
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
Example shared_subdistribution_mass {A} (mu : FiniteSubdist R A) :
  finite_subdist_expect (finite_subdist_positions mu) (fun _ => 1) = finite_subdist_expect mu (fun _ => 1).
Proof. exact: finite_subdist_positions_expect. Qed.
Example shared_subdistribution_bound {A} (mu : FiniteSubdist R A) :
  finite_mass (finite_subdist_enum (finite_subdist_positions mu)) <= 1.
Proof. exact: finite_subdist_mass_bound. Qed.
Example shared_subdistribution_decode {A} (mu : FiniteSubdist R A) :
  finite_enum_raw (finite_subdist_enum
    (finite_subdist_map (finite_position_value (finite_enum_raw (finite_subdist_enum mu)))
      (finite_subdist_positions mu))) = finite_enum_raw (finite_subdist_enum mu).
Proof. exact: finite_subdist_positions_decode. Qed.
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
