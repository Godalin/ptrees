(** Reasoning entry point. Export the actual theorem owners, not aliases.
    Eq/Bind owns the heterogeneous peutt_bind theorem; backends provide only
    probability-level algebra/order/limit obligations. *)
From PTree Require Export PTree Eq.
From PTree.Eq Require Export UnifiedFrontier PrimitiveStableHitting
  WellFormedness StableHittingComputation ProbabilisticTrace Bind Algebra.
From PTree.Eq.FreeOmega Require Export Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Export Guarded Atomic MDP.
