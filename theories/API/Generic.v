(** Role: User-facing assembly or tree/backend adapter. Imports lower layers explicitly; not new semantic theory. *)
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
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import WellFormedness.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PStruct PStrong PEutt StableHittingComputation ProbabilisticTrace.
From PTree.API Require Import Behavior.

(** Curated aliases are declared here because [Require Import] deliberately
    does not re-export the short names introduced by implementation modules. *)
Notation ptree := PTreeDefinition.ptree.
Notation Ret x := (PTreeDefinition.Ret x).
Notation Tau t := (PTreeDefinition.Tau t).
Notation Vis e k := (PTreeDefinition.Vis e k).
Notation Prob mu k := (PTreeDefinition.Prob mu k).
Notation bind := PTreeDefinition.PTree.bind.
Notation iter := PTreeDefinition.PTree.iter.
Notation interp := PTreeDefinition.PTree.interp.
Notation translate := PTreeDefinition.PTree.translate.
Notation probabilistic_ptree := WellFormedness.probabilistic_ptree.
Notation probabilistic_ptree_ret := WellFormedness.probabilistic_ptree_ret.
Notation probabilistic_ptree_tau := WellFormedness.probabilistic_ptree_tau.
Notation probabilistic_ptree_vis := WellFormedness.probabilistic_ptree_vis.
Notation probabilistic_ptree_prob := WellFormedness.probabilistic_ptree_prob.
Notation probabilistic_ptree_bind := WellFormedness.probabilistic_ptree_bind.
Notation probabilistic_ptree_iter := WellFormedness.probabilistic_ptree_iter.
Notation stable_head := UnifiedFrontier.stable_head.
Notation stable_head_rel := UnifiedFrontier.stable_head_rel.
Notation stable_hitting := PrimitiveStableHitting.stable_hitting.
Notation pstruct := PStruct.pstruct.
Notation pstrong := PStrong.pstrong.
Notation peutt := PEutt.peutt.
Notation finite_interaction_pattern :=
  ProbabilisticTrace.finite_interaction_pattern.
Notation finite_interaction_query := ProbabilisticTrace.finite_interaction_query.
Notation finite_interaction_sem := ProbabilisticTrace.finite_interaction_sem.

(** Only the public glyph chooses the canonical profile. The raw [peutt]
    alias above remains available for explicitly parameterized theory. *)
Notation "t ≈ₚ[ RR ] u" := (Behavior.canonical_peutt RR t u)
  (at level 70, RR at next level, no associativity) : type_scope.
Notation "t ≈ₚ u" := (Behavior.canonical_peutt eq t u)
  (at level 70, no associativity) : type_scope.

(** Stable-hitting and behavioral endpoints. *)
Notation stable_hitting_exists :=
  PrimitiveStableHitting.stable_hitting_exists.
Notation stable_hitting_unique :=
  PrimitiveStableHitting.stable_hitting_unique.
Notation stable_hitting_ret := PEutt.stable_hitting_ret.
Notation stable_hitting_vis := PEutt.stable_hitting_vis.
Notation stable_hitting_tau_iff := PEutt.stable_hitting_tau_iff.
Notation stable_hitting_tau := StableHittingComputation.stable_hitting_tau.
Notation stable_hitting_tau_iter := StableHittingComputation.stable_hitting_tau_iter.
Notation stable_hitting_prob := PEutt.stable_hitting_prob.
Notation stable_hitting_bind := PEutt.stable_hitting_bind.
Notation stable_hitting_ret_iff := StableHittingComputation.stable_hitting_ret_iff.
Notation stable_hitting_vis_iff := StableHittingComputation.stable_hitting_vis_iff.
Notation stable_hitting_prob_decompose :=
  StableHittingComputation.stable_hitting_prob_decompose.
Notation stable_hitting_prob_compute :=
  StableHittingComputation.stable_hitting_prob_compute.
Notation stable_hitting_prob_dirac :=
  StableHittingComputation.stable_hitting_prob_dirac.
Notation stable_hitting_prob_flatten :=
  StableHittingComputation.stable_hitting_prob_flatten.
Notation peutt_iff_hitting := StableHittingComputation.peutt_iff_hitting.
Notation peutt_of_hitting_lift := PEutt.peutt_of_hitting_lift.
Notation peutt_hitting_lift := PEutt.peutt_hitting_lift.
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
Notation peutt_prob_rewrite := PEutt.peutt_prob_rewrite.
(** Unconditional public [peutt_bind] is supplied by API/FreeOmega.
    This generic facade retains the arbitrary-frontier theorem and its
    explicit scheduling premise. PTree exports API/FreeOmega after this
    facade, selecting the unconditional corollary for ordinary clients. *)
Notation peutt_bind := PEutt.peutt_bind.
Notation pstruct_pstrong := PStrong.pstruct_pstrong.
Notation pstruct_equivalence := PStruct.pstruct_equivalence.
Notation pstrong_equivalence := PStrong.pstrong_equivalence.
Notation pstrong_bind := PStrong.pstrong_bind.
Notation peutt_rewrite_l := PEutt.peutt_rewrite_l.
Notation peutt_rewrite_r := PEutt.peutt_rewrite_r.
Notation peutt_rewrite := PEutt.peutt_rewrite.

(** Finite-cylinder adequacy and extensionality endpoints. *)
Notation finite_interaction_sem_spec :=
  ProbabilisticTrace.finite_interaction_sem_spec.
Notation peutt_preserves_finite_interaction_sem :=
  ProbabilisticTrace.peutt_preserves_finite_interaction_sem.
