(** Curated comparison-semantics entry point; not a replacement for peutt. *)
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim MDPFragment MDPCoincidence.
Notation head_step := HeadTransition.head_step.
Notation head_bisim := HeadTransition.head_bisim.
Notation tree_trans := TreeTransition.tree_trans.
Notation tree_return_observation := TreeTransition.tree_return_observation.
Notation tree_offered_event_observation := TreeTransition.tree_offered_event_observation.
Notation tree_trans_bisim := TreeTransitionBisim.tree_trans_bisim.
Notation tree_trans_bisim_coinduction := TreeTransitionBisim.tree_trans_bisim_coinduction.
Notation mdp_head := MDPFragment.mdp_head.
Notation mdp_state := MDPFragment.mdp_state.
