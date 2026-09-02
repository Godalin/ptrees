Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

(** Public generic facade for the semantic architecture:

      PTree representation
        -> primitive kernel and stable hitting
        -> probabilistic_eutt / finite interaction observations.

    The historical module names remain available to proof developers, while
    clients need not treat frontier certificates or operational compatibility
    aliases as additional semantic layers. *)
(** Deliberately import, rather than transitively export, implementation
    modules.  Requiring this facade loads the definitions needed by the
    curated surface below without turning their module imports and scopes
    into part of the facade contract. *)
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import
  UnifiedFrontier
  PrimitiveStableHitting
  ProbabilisticEutt
  ProbabilisticTrace.

(** Curated aliases are declared here because [Require Import] deliberately
    does not re-export the short names introduced by implementation modules. *)
Notation ptree := PTreeDefinition.ptree.
Notation stable_head := UnifiedFrontier.frontier_head.
Notation stable_head_rel := UnifiedFrontier.stable_head_rel.
Notation stable_hitting := PrimitiveStableHitting.stable_hitting.
Notation probabilistic_eutt := ProbabilisticEutt.probabilistic_eutt.
Notation finite_interaction_pattern :=
  ProbabilisticTrace.finite_interaction_pattern.
Notation finite_interaction_query := ProbabilisticTrace.finite_interaction_query.
Notation finite_interaction_sem := ProbabilisticTrace.finite_interaction_sem.

Notation "t ≈ₚ[ RR ] u" := (probabilistic_eutt RR t u)
  (at level 70, RR at next level, no associativity) : type_scope.
Notation "t ≈ₚ u" := (probabilistic_eutt eq t u)
  (at level 70, no associativity) : type_scope.

(** Stable-hitting and behavioral endpoints. *)
Notation stable_hitting_exists :=
  PrimitiveStableHitting.stable_hitting_exists.
Notation stable_hitting_unique :=
  PrimitiveStableHitting.stable_hitting_unique.
Notation probabilistic_eutt_coinduction :=
  ProbabilisticEutt.probabilistic_eutt_coinduction.
Notation probabilistic_eutt_refl := ProbabilisticEutt.probabilistic_eutt_refl.
Notation probabilistic_eutt_sym := ProbabilisticEutt.probabilistic_eutt_sym.
Notation probabilistic_eutt_trans := ProbabilisticEutt.probabilistic_eutt_trans.
Notation probabilistic_eutt_ret := ProbabilisticEutt.probabilistic_eutt_ret.
Notation probabilistic_eutt_tau_l := ProbabilisticEutt.probabilistic_eutt_tau_l.
Notation probabilistic_eutt_tau_r := ProbabilisticEutt.probabilistic_eutt_tau_r.
Notation probabilistic_eutt_vis := ProbabilisticEutt.probabilistic_eutt_vis.
Notation probabilistic_eutt_prob := ProbabilisticEutt.probabilistic_eutt_prob.
Notation probabilistic_eutt_bind := ProbabilisticEutt.probabilistic_eutt_bind.

(** Finite-cylinder adequacy and extensionality endpoints. *)
Notation finite_interaction_sem_spec :=
  ProbabilisticTrace.finite_interaction_sem_spec.
Notation probabilistic_eutt_preserves_finite_interaction_sem :=
  ProbabilisticTrace.probabilistic_eutt_preserves_finite_interaction_sem.
