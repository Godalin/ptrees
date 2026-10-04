(** The language's generic mathematics is independent of both completion
    syntax and validating models. Concrete clients remain ordinary Gate S. *)
From Coq Require Import Utf8.
From PTree.Examples.PGCL Require Import Syntax Forward Algebra Interpretation Adequacy StateInterpretation.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.mathcomp_tree.
Check @pgcl_forward_correspondence.
Check @run_execute.
Check @denote_while_least.
Check @cequiv_denotes.
Check @while_Proper.
Check @seq_skip_r.

From PTree.Examples.PGCL Require Import FreeOmega Finite Programs RandomWalk.
Check @pgcl_run_denotes_iff.
Check @rational_pgcl_hitting.
Check @real_pgcl_hitting.
Check @CoinLoops.partial_frontier.
Check @walk_run.
Check @walk_denote_closed_form.
Check @pgcl_run_Proper.
Check @pgcl_while_least_fixed_point.
Check @PTree.Prob.FreeOmega.IterationOrder.free_omega_iter_least_fixed_point.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.mathcomp_tree.
