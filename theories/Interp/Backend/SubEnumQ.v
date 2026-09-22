(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.Total.
From PTree.Eq Require Import PEutt.
From PTree.Semantics Require Import MDPFragment.
From PTree.Interp.FreeOmega Require Import Atomic MDP.
From PTree.Semantics Require Import TreeTransitionBisim.
From PTree.Semantics.FreeOmega Require Import MDPCoincidenceFreeOmega.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SubEnumQMDPInterp.
Context {E : Type -> Type} {R : Type}.
Variable handler : forall X, E X -> ptree E SubEnumQ X.
Variable atom : atomic_handler (NI := SubEnumQ_SemanticMeasure)
  (NO := SubEnumQ_SemanticOmega) handler.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation state := (@mdp_state E SubEnumQ MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation W := (@peutt E SubEnumQ MF FI FC FreeOmegaMixedMeasure FO R R eq).
Local Notation TB := (@tree_trans_bisim E SubEnumQ MF FI FC FreeOmegaMixedMeasure FO R R eq).

(** No unproved total-map side condition remains on this canonical
    backend. In particular successor measures need not be finite or Dirac. *)
Theorem subenumQ_atomic_handler_mdp :
  mdp_handler (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)
    (R := R) handler.
Proof.
  apply (atomic_handler_mdp (atom := atom)). intros mu Hmu.
  exact (subenumQ_free_omega_total_map (atomic_head atom) Hmu).
Qed.

Theorem subenumQ_mdp_state_interp_atomic t : state t -> state (PTree.interp handler t).
Proof. apply mdp_state_interp. exact subenumQ_atomic_handler_mdp. Qed.

Theorem subenumQ_mdp_interp_peutt_tree_trans_iff t u : state t -> state u ->
  (W (PTree.interp handler t) (PTree.interp handler u) <->
   TB (PTree.interp handler t) (PTree.interp handler u)).
Proof. apply mdp_interp_peutt_tree_trans_iff. exact subenumQ_atomic_handler_mdp. Qed.

(** The two compositionality routes meet in the preserved fragment.
    This is preservation, NOT reflection back to the source programs. *)
Theorem subenumQ_mdp_interp_transition_to_peutt t u :
  state t -> state u -> TB t u ->
  W (PTree.interp handler t) (PTree.interp handler u).
Proof.
  intros Ht Hu Htu.
  apply (proj2 (subenumQ_mdp_interp_peutt_tree_trans_iff Ht Hu)).
  exact (tree_trans_bisim_interp_atomic atom Htu).
Qed.

End SubEnumQMDPInterp.
