(** Compatibility entry point for the FreeOmega canonical equality library.

    The implementation is being split into focused facts, rewriting,
    iteration, and interpretation modules.  Keeping this module as the
    stable aggregate means existing developments do not need to change their
    imports while that refactoring proceeds. *)
From PTree.Eq Require Export
  OperationalProbabilisticPTSFreeOmegaBase
  OperationalProbabilisticPTSFreeOmegaFacts
  OperationalProbabilisticPTSFreeOmegaInterp.
