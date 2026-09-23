(** Reasoning entry point. Export the actual theorem owners, not aliases.
    The generic bind theorem is peutt_bind_cofinal; the unconditional
    observable FreeOmega theorem is the unique peutt_bind. *)
From PTree Require Export PTree Eq.
From PTree.Eq Require Export UnifiedFrontier PrimitiveStableHitting
  WellFormedness StableHittingComputation ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Export Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Export Guarded Atomic MDP.
