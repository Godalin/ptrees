(** Curated comparison-semantics entry point; not a replacement for peutt. *)
From PTree.Semantics Require Import HeadTransition TreeTransition TreeTransitionBisim MDPFragment.
Notation head_step := HeadTransition.head_step.
Notation head_bisim := HeadTransition.head_bisim.
Notation trans := TreeTransition.trans.
Notation tree_return_observation := TreeTransition.tree_return_observation.
Notation tree_offered_event_observation := TreeTransition.tree_offered_event_observation.
Notation trans_bisim := TreeTransitionBisim.trans_bisim.
Notation trans_bisim_coinduction := TreeTransitionBisim.trans_bisim_coinduction.
Notation mdp_head := MDPFragment.mdp_head.
Notation mdp_state := MDPFragment.mdp_state.
