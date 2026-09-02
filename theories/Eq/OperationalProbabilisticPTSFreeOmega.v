(** Stable aggregate entry point for the FreeOmega canonical equality
    library.  Operational foundations, backend facts, rewriting, iteration,
    interpretation, and quantitative stable-head queries live in focused
    modules; existing developments may continue importing this compatibility
    module. *)
From PTree.Eq Require Export
  ProbabilisticTrace
  OperationalProbabilisticPTSFreeOmegaBase
  OperationalProbabilisticPTSFreeOmegaFacts
  OperationalProbabilisticPTSFreeOmegaRewrite
  OperationalProbabilisticPTSFreeOmegaIter
  OperationalProbabilisticPTSFreeOmegaInterp.
