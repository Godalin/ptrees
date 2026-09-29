(** Role: Independent loading and export contracts for syntax, relations,
    reasoning and comparison semantics. Qualified failures test loading. *)
From PTree Require Import PTree.
Check @ptree.
Check @bind.
Check @Handler.cat.
Check (Ret tt : ptree (fun _ => Empty_set) (fun A => A) unit).
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Eq.Canonical.CanonicalBehavior.

From PTree Require Import Eq.
Check @pstruct.
Check @pstrong.
Check @peutt.
Check @canonical_peutt.
Check @peutt_bind_cofinal.
Fail Check PTree.Eq.Bind.peutt_bind.
Fail Check PTree.Interp.Kernel.ptree_interp_head_tree.
Fail Definition no_default_backend {E MN R} (t : ptree E MN R) : Prop := t ≈ₚ t.

From PTree Require Semantics.
Module ComparisonBoundary.
Import Semantics.
Check @trans.
Check @trans_bisim.
Check @trans_bisim_refl.
Check @trans_bisim_sym.
Check @trans_bisim_trans.
Check @trans_bisim_equivalence.
Check @peutt_trans_bisim.
Check @mdp_state_peutt_trans_iff.
Check @mdp_trans_bisim_iff.
Check @tree_return_observation.
Check @tree_offered_event_observation.
Check @head_step.
Check @head_bisim.
Fail Check PTree.Semantics.TreeTransition.tree_trans.
Fail Check PTree.Semantics.TreeTransitionBisim.tree_trans_bisim.
Check @mdp_state.
Fail Check PTree.Interp.FreeOmega.Atomic.atomic_handler.
Fail Check PTree.Prob.Backend.SubEnumQ.Representation.SubEnumQ.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.
End ComparisonBoundary.

From PTree Require Import PTreeFacts.
Check @peutt_bind.
Check @peutt_bind_assoc.
Check @peutt_iter_rel.
Check @peutt_interp_guarded.
Check @mdp_guarded_interp_trans.
Check @ptree_bind_cofinal_all.
Check @peutt_interp_handler_rel.
Check @free_omega_peutt_interp_handler_rel.
Check @handler_cat_assoc.
Check @run_state_peutt.
Check @run_reader_peutt.
Check @run_writer_peutt.
Check @run_exception_peutt.
Fail Check PTree.Eq.Internal.FiniteInternal.finite_internal.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.Backend.SubEnumQ.Representation.SubEnumQ.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.
