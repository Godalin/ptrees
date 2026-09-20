(** Role: User-facing assembly or tree/backend adapter. Imports lower layers explicitly; not new semantic theory. *)
(** Curated canonical-model API. Uses FreeOmega equational/interpreter theory;
    exposes endpoint names, not quotient lifts, schedules or acceleration grids. *)
From PTree.Eq.FreeOmega Require Import Algebra Iter Relation.
From PTree.Interp.FreeOmega Require Import Base Guarded Atomic MDP.
Notation peutt_bind_assoc := Algebra.peutt_bind_assoc.
Notation peutt_bind_ret_l := Algebra.peutt_bind_ret_l.
Notation peutt_bind_ret_r := Algebra.peutt_bind_ret_r.
Notation peutt_iter_rel := Iter.peutt_iter_rel.
Notation peutt_iter_unfold := Iter.peutt_iter_unfold.
Notation guarded_handler := Guarded.guarded_handler.
Notation peutt_interp_guarded := Guarded.peutt_interp_guarded.
Notation peutt_interp_guarded_Proper := Guarded.peutt_interp_guarded_Proper.
Notation atomic_handler := Atomic.atomic_handler.
Notation tree_trans_bisim_interp_atomic := Atomic.tree_trans_bisim_interp_atomic.
Notation mdp_handler := MDP.mdp_handler.
Notation mdp_state_interp := MDP.mdp_state_interp.
Notation mdp_guarded_interp_tree_trans := MDP.mdp_guarded_interp_tree_trans.
