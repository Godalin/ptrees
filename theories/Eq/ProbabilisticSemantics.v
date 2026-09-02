Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

(** Public generic facade for the semantic architecture:

      PTree representation
        -> primitive kernel and stable hitting
        -> probabilistic_eutt / finite interaction observations.

    The historical module names remain available to proof developers, while
    clients need not treat frontier certificates or operational compatibility
    aliases as additional semantic layers. *)
From PTree.Core Require Export PTreeDefinition.
From PTree.Eq Require Export
  UnifiedFrontier
  PrimitiveStableHitting
  OperationalProbabilisticPTS
  ProbabilisticEutt
  ProbabilisticTrace.
