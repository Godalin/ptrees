(** Curated comparison-semantics entry point; not a replacement for peutt. *)
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim MDPFragment.
From PTree.Semantics Require Import TreeTransitionSoundness MDPCoincidence MDPReflection.
Notation head_step := HeadTransition.head_step.
Notation head_bisim := HeadTransition.head_bisim.
Notation trans := TreeTransition.trans.
Notation tree_return_observation := TreeTransition.tree_return_observation.
Notation tree_offered_event_observation := TreeTransition.tree_offered_event_observation.
Notation trans_bisim := TreeTransitionBisim.trans_bisim.
Notation trans_bisim_coinduction := TreeTransitionBisim.trans_bisim_coinduction.
Notation trans_bisim_refl := TreeTransitionBisim.trans_bisim_refl.
Notation trans_bisim_sym := TreeTransitionBisim.trans_bisim_sym.
Notation trans_bisim_trans := TreeTransitionBisim.trans_bisim_trans.
Notation trans_bisim_equivalence := TreeTransitionBisim.trans_bisim_equivalence.
Notation mdp_head := MDPFragment.mdp_head.
Notation mdp_state := MDPFragment.mdp_state.
(** Generic comparison chain; backend-specific probability obligations stay
    explicit. No concrete backend or interpreter is selected by this facade. *)
Notation peutt_trans_bisim := TreeTransitionSoundness.peutt_trans_bisim.
Notation mdp_state_peutt_trans_iff := MDPCoincidence.mdp_state_peutt_trans_iff.
Notation mdp_trans_bisim_iff := MDPReflection.mdp_trans_bisim_iff.
