(** Role: Main native-parametric external soundness entry point for FreeOmega.
    Concrete backends discharge native interpretation obligations, not a
    second copy of the completion proof. This is external validation only;
    maintained PTree reasoning must never import this entry point.

    Model: modelable_iff_denotes.
    Quotient: model_qlift_eq_sound, model_qlift_bidual.
    Order: free_omega_sem_le_sound (modelable endpoints only).
    Iteration: free_omega_iteration_modelable, free_omega_iteration_denotes_lfp.
    PTree: stable_hitting_modelable, stable_hitting_denotational_adequacy.

    No actual-joint existence for an arbitrary native backend is claimed.
    Such realization remains a separate backend-specific theorem. *)
From PTree.Prob.FreeOmega.Validation Require Export
  Model Continuity Observation Relational Quotient DomainOrder Iteration StableHitting.
