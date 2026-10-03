(** The language's generic mathematics is independent of both completion
    syntax and validating models. Concrete clients remain ordinary Gate S. *)
From Coq Require Import Utf8.
From PTree.Examples.PGCL Require Import Syntax Forward Interpretation Adequacy StateInterpretation.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.mathcomp_tree.
Check @pgcl_forward_correspondence.
Check @run_execute.
Check @denote_while_least.

From PTree.Examples.PGCL Require Import FreeOmega Finite Programs RandomWalk.
Check @pgcl_run_denotes_iff.
Check @rational_pgcl_hitting.
Check @real_pgcl_hitting.
Check @CoinLoops.partial_frontier.
Check @walk_run.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.Backend.MathComp.mathcomp_tree.
