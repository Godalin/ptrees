Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

(** Public generic facade for the semantic architecture:

      PTree representation
        -> primitive kernel and stable hitting
        -> peutt / finite interaction observations.

    Proof-oriented frontier certificates remain implementation
    infrastructure rather than an additional semantic layer. *)
(** Deliberately import, rather than transitively export, implementation
    modules.  Requiring this facade loads the definitions needed by the
    curated surface below without turning their module imports and scopes
    into part of the facade contract. *)
From PTree.Core Require Import PTreeDefinition PTreeProbability.
From PTree.Eq Require Import
  UnifiedFrontier
  PrimitiveStableHitting
  PStruct
  PStrong
  PFinite
  PEutt
  ProbabilisticTrace.

(** Curated aliases are declared here because [Require Import] deliberately
    does not re-export the short names introduced by implementation modules. *)
Notation ptree := PTreeDefinition.ptree.
Notation probabilistic_ptree := PTreeProbability.probabilistic_ptree.
Notation probabilistic_ptree_ret := PTreeProbability.probabilistic_ptree_ret.
Notation probabilistic_ptree_tau := PTreeProbability.probabilistic_ptree_tau.
Notation probabilistic_ptree_vis := PTreeProbability.probabilistic_ptree_vis.
Notation probabilistic_ptree_prob := PTreeProbability.probabilistic_ptree_prob.
Notation probabilistic_ptree_bind := PTreeProbability.probabilistic_ptree_bind.
Notation probabilistic_ptree_iter := PTreeProbability.probabilistic_ptree_iter.
Notation stable_head := UnifiedFrontier.frontier_head.
Notation stable_head_rel := UnifiedFrontier.stable_head_rel.
Notation stable_hitting := PrimitiveStableHitting.stable_hitting.
Notation pstruct := PStruct.pstruct.
Notation pstrong := PStrong.pstrong.
Notation pfinite := PFinite.pfinite.
Notation peutt := PEutt.peutt.
Notation finite_interaction_pattern :=
  ProbabilisticTrace.finite_interaction_pattern.
Notation finite_interaction_query := ProbabilisticTrace.finite_interaction_query.
Notation finite_interaction_sem := ProbabilisticTrace.finite_interaction_sem.

Notation "t ≈ₚ[ RR ] u" := (peutt RR t u)
  (at level 70, RR at next level, no associativity) : type_scope.
Notation "t ≈ₚ u" := (peutt eq t u)
  (at level 70, no associativity) : type_scope.

(** Stable-hitting and behavioral endpoints. *)
Notation stable_hitting_exists :=
  PrimitiveStableHitting.stable_hitting_exists.
Notation stable_hitting_unique :=
  PrimitiveStableHitting.stable_hitting_unique.
Notation peutt_coinduction :=
  PEutt.peutt_coinduction.
Notation peutt_refl := PEutt.peutt_refl.
Notation peutt_sym := PEutt.peutt_sym.
Notation peutt_trans := PEutt.peutt_trans.
Notation peutt_equivalence := PEutt.peutt_equivalence.
Notation peutt_ret := PEutt.peutt_ret.
Notation peutt_tau_l := PEutt.peutt_tau_l.
Notation peutt_tau_r := PEutt.peutt_tau_r.
Notation peutt_vis := PEutt.peutt_vis.
Notation peutt_prob := PEutt.peutt_prob.
Notation peutt_bind := PEutt.peutt_bind.
Notation pstruct_pstrong := PStrong.pstruct_pstrong.
Notation pstruct_equivalence := PStruct.pstruct_equivalence.
Notation pstrong_equivalence := PStrong.pstrong_equivalence.
Notation pstrong_bind := PStrong.pstrong_bind.
Notation pstrong_pfinite := PFinite.pstrong_pfinite.
Notation pfinite_rel_mono := PFinite.pfinite_rel_mono.
Notation pfinite_equivalence := PFinite.pfinite_equivalence.
Notation pfinite_sym := PFinite.pfinite_sym.
Notation pfinite_tau_l := PFinite.pfinite_tau_l.
Notation pfinite_tau_r := PFinite.pfinite_tau_r.
Notation peutt_rewrite_l := PEutt.peutt_rewrite_l.
Notation peutt_rewrite_r := PEutt.peutt_rewrite_r.
Notation peutt_rewrite := PEutt.peutt_rewrite.

(** Finite-cylinder adequacy and extensionality endpoints. *)
Notation finite_interaction_sem_spec :=
  ProbabilisticTrace.finite_interaction_sem_spec.
Notation peutt_preserves_finite_interaction_sem :=
  ProbabilisticTrace.peutt_preserves_finite_interaction_sem.
