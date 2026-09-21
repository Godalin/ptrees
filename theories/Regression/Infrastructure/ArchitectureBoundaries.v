(** Role: import-contract regression for the public entry points and Core.
    Qualified Fail checks test loading; short-name checks test API exposure. *)
From PTree.Core Require PTreeDefinition.
Module CoreLoadingBoundary.
Import PTreeDefinition.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Eq.PEutt.peutt.
End CoreLoadingBoundary.

From PTree Require Semantics.
Module ComparisonFacadeBoundary.
Import Semantics.
Check @tree_trans.
Check @tree_trans_bisim.
Check @mdp_state.
Fail Check PTree.Interp.Kernel.ptree_interp_head_tree.
Fail Check PTree.Interp.FreeOmega.Atomic.atomic_handler.
Fail Check head_action_result.
Fail Check tree_trans_bisimF.
End ComparisonFacadeBoundary.

From PTree Require PTree.
Module CanonicalFacadeBoundary.
Import PTree.
Check @ptree.
Check (Ret tt : ptree (fun _ => Empty_set) (fun A => A) unit).
Check @bind.
Check @peutt.
Check @peutt_bind_assoc.
Check @peutt_iter_rel.
Check @peutt_interp_guarded.
Check @mdp_guarded_interp_tree_trans.
Fail Check free_omega_qlift.
Fail Check ptree_interp_split_approx.
Fail Check interp_bisim_candidate.
Fail Check atomic_candidate.
Fail Check finite_internal.
Fail Check kernel_completion_invariant.
Fail Check PTree.Prob.Backend.SubEnum.Measure.SubEnum.
End CanonicalFacadeBoundary.
