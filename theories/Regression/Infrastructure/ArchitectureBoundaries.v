(** Role: Independent loading and export contracts for syntax, relations,
    reasoning and comparison semantics. Qualified failures test loading. *)
From PTree Require Import PTree.
Check @ptree.
Check @bind.
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
Fail Check PTree.Eq.FreeOmega.Bind.peutt_bind.
Fail Check PTree.Interp.Kernel.ptree_interp_head_tree.
Fail Definition no_default_backend {E MN R} (t : ptree E MN R) : Prop := t ≈ₚ t.

From PTree Require Semantics.
Module ComparisonBoundary.
Import Semantics.
Check @tree_trans.
Check @tree_trans_bisim.
Check @mdp_state.
Fail Check PTree.Interp.FreeOmega.Atomic.atomic_handler.
End ComparisonBoundary.

From PTree Require Import PTreeFacts.
Check @peutt_bind.
Check @peutt_bind_assoc.
Check @peutt_iter_rel.
Check @peutt_interp_guarded.
Check @mdp_guarded_interp_tree_trans.
Check @ptree_bind_cofinal_all.
Fail Check PTree.Eq.Internal.FiniteInternal.finite_internal.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.Backend.SubEnumQ.Representation.SubEnumQ.
Fail Check PTree.Eq.Backend.MathComp.Direct.MathComp_CanonicalBehavior.
