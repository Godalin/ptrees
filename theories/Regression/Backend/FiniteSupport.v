(** Container nonnegativity is essential once coefficients are ordinary rat.
    Positive/zero support facts work for both rat and arbitrary realType. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms FiniteSupport.
Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Set Implicit Arguments.
Unset Strict Implicit.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Example ordinary_rat_zero_atom {A : eqType}
    (mu : FiniteEnum rat_rat__canonical__Num_NumDomain A) x :
  finite_atom x (finite_enum_raw mu) = 0 <->
    forall p, List.In (p,x) (finite_enum_raw mu) -> p = 0.
Proof. exact (finite_atom_zero_iff x (finite_enum_nonnegative mu)). Qed.

Example real_positive_atom (R : realType) {A : eqType}
    (mu : FiniteEnum R A) x :
  0 < finite_atom x (finite_enum_raw mu) <->
    exists p, List.In (p,x) (finite_enum_raw mu) /\ p <> 0.
Proof. exact (finite_atom_positive_iff x (finite_enum_nonnegative mu)). Qed.

Example function_values_have_indicator_support
    (mu : FiniteEnum rat_rat__canonical__Num_NumDomain (nat -> nat)) P :
  0 < finite_enum_expect mu (fun f => if P f then 1 else 0) ->
    exists p f, List.In (p,f) (finite_enum_raw mu) /\ p <> 0 /\ P f.
Proof. exact: finite_indicator_positive_member. Qed.

Example duplicate_zero_entries :
  finite_atom true [:: ((0:rat),true); (1,true); (0,false); (2,true)] = 3.
Proof. by vm_compute. Qed.

Example negative_cancellation_has_zero_atom :
  finite_atom true [:: ((1:rat),true); (-1,true)] = 0.
Proof. by vm_compute. Qed.

Example negative_cancellation_not_nonnegative :
  ~ finite_nonnegative [:: ((1:rat),true); (-1,true)].
Proof.
  move=> H.
  have Hneg := H (-1) true (or_intror (or_introl (Logic.eq_refl _))).
  by vm_compute in Hneg.
Qed.

Example zero_atom_without_nonnegative_cannot_kill_entries :
  ~ (forall p, List.In (p,true) [:: ((1:rat),true); (-1,true)] -> p = 0).
Proof.
  move=> H; have Hbad := H 1 (or_introl (Logic.eq_refl _)).
  by vm_compute in Hbad.
Qed.

Section Universes.
Universe u.
Example high_carrier_indicator_support
    (mu : FiniteEnum rat_rat__canonical__Num_NumDomain Type@{u}) P :
  0 < finite_enum_expect mu (fun X => if P X then 1 else 0) ->
    exists p X, List.In (p,X) (finite_enum_raw mu) /\ p <> 0 /\ P X.
Proof. exact: finite_indicator_positive_member. Qed.
End Universes.
