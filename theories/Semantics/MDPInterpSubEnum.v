Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  FreeOmegaMeasure FreeOmegaTotalSubEnum.
From PTree.Eq Require Import PEutt.
From PTree.Semantics Require Import MDPFragment AtomicInterp MDPInterp
  TreeTransitionBisim MDPCoincidenceFreeOmega.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SubEnumMDPInterp.
Context {E : Type -> Type} {R : Type}.
Variable handler : forall X, E X -> ptree E SubEnum X.
Variable atom : atomic_handler (NI := SubEnum_SemanticMeasure)
  (NO := SubEnum_SemanticOmega) handler.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation state := (@mdp_state E SubEnum MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation W := (@peutt E SubEnum MF FI FC FreeOmegaMixedMeasure FO R R eq).
Local Notation TB := (@tree_trans_bisim E SubEnum MF FI FC FreeOmegaMixedMeasure FO R R eq).

(** No unproved total-map side condition remains on this canonical
    backend. In particular successor measures need not be finite or Dirac. *)
Theorem subenum_atomic_handler_mdp :
  mdp_handler (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)
    (R := R) handler.
Proof.
  apply (atomic_handler_mdp (atom := atom)). intros mu Hmu.
  exact (subenum_free_omega_total_map (atomic_head atom) Hmu).
Qed.

Theorem subenum_mdp_state_interp_atomic t : state t -> state (PTree.interp handler t).
Proof. apply mdp_state_interp. exact subenum_atomic_handler_mdp. Qed.

Theorem subenum_mdp_interp_peutt_tree_trans_iff t u : state t -> state u ->
  (W (PTree.interp handler t) (PTree.interp handler u) <->
   TB (PTree.interp handler t) (PTree.interp handler u)).
Proof. apply mdp_interp_peutt_tree_trans_iff. exact subenum_atomic_handler_mdp. Qed.

(** The two compositionality routes meet in the preserved fragment.
    This is preservation, NOT reflection back to the source programs. *)
Theorem subenum_mdp_interp_transition_to_peutt t u :
  state t -> state u -> TB t u ->
  W (PTree.interp handler t) (PTree.interp handler u).
Proof.
  intros Ht Hu Htu.
  apply (proj2 (subenum_mdp_interp_peutt_tree_trans_iff Ht Hu)).
  exact (tree_trans_bisim_interp_atomic atom Htu).
Qed.

End SubEnumMDPInterp.
