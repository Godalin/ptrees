(** Stable aggregate entry point for the FreeOmega canonical equality
    library.  Operational foundations, backend facts, rewriting, iteration,
    and interpretation live in focused modules; existing developments may
    continue importing this compatibility module. *)
From PTree.Eq Require Export
  OperationalProbabilisticPTSFreeOmegaBase
  OperationalProbabilisticPTSFreeOmegaFacts
  OperationalProbabilisticPTSFreeOmegaRewrite
  OperationalProbabilisticPTSFreeOmegaIter
  OperationalProbabilisticPTSFreeOmegaInterp.
