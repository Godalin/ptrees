(** Canonical entry point for the FreeOmega realization of PTree semantics.
    Backend-neutral relations remain in [PTree.Eq]; this module collects the
    FreeOmega-specific semantic proofs and equational endpoints. *)
From PTree.Eq Require Export ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Export
  Base Relation Bind Algebra Iter Interp.
