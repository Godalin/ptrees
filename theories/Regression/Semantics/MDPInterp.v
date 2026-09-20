Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum
  FreeOmegaMeasure FreeOmegaTotalSubEnum.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt.
From PTree.Semantics Require Import MDPFragment AtomicInterp MDPInterp
  MDPInterpSubEnum TreeTransitionBisim.
From PTree.Regression.Semantics Require Import MDPFragment MDPCoincidence AtomicInterp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).
Local Notation state := (@mdp_state decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit).
Local Notation W := (@peutt decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit unit eq).
Local Notation TB := (@tree_trans_bisim decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit unit eq).

(** Rename observable replies, retain the request event, and insert the
    same internal Prob/Tau response plumbing tested in stage 3. *)
Definition flip_reply X (e : decisionE X) : decisionE X :=
  match e in decisionE X return decisionE X with
  | Ask => Ask | Reply b => Reply (negb b)
  end.
Lemma flip_reply_involution X (e : decisionE X) : flip_reply (flip_reply e) = e.
Proof. destruct e; [reflexivity|]. destruct b; reflexivity. Qed.
Definition mdp_test_handler X (e : decisionE X) : ptree decisionE SubEnum X :=
  Tau (Vis (flip_reply e) (fun x => delayed_response x)).
Definition mdp_test_atomic : atomic_handler
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega) mdp_test_handler.
Proof.
  refine {| atomic_rename := @flip_reply;
            atomic_unrename := @flip_reply;
            atomic_cont := fun X e x => delayed_response x |}.
  - exact flip_reply_involution.
  - exact flip_reply_involution.
  - intros X e. apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
  - intros X e x. apply delayed_response_hitting.
Defined.

Example request_sample_reply_stays_mdp :
  state (PTree.interp mdp_test_handler decision).
Proof. exact (subenum_mdp_state_interp_atomic mdp_test_atomic visible_sample_visible_is_mdp). Qed.

Example infinite_service_stays_mdp b :
  state (PTree.interp mdp_test_handler (service b)).
Proof. exact (subenum_mdp_state_interp_atomic mdp_test_atomic (infinite_service_mdp b)). Qed.

Example delayed_initial_state_stays_mdp :
  state (PTree.interp mdp_test_handler (Tau (Tau decision))).
Proof. exact (subenum_mdp_state_interp_atomic mdp_test_atomic delayed_decision_is_mdp). Qed.

Example terminal_state_stays_mdp : state (PTree.interp mdp_test_handler (Ret tt)).
Proof.
  apply (subenum_mdp_state_interp_atomic mdp_test_atomic).
  apply mdp_state_ret.
Qed.

(** Not a Dirac-only proof: the action successor here is the existing
    non-Dirac hidden_choice. The fragment does not require that subtree
    itself to be a state. *)
Example distribution_not_state_boundary :
  ~ state hidden_choice /\ state (PTree.interp mdp_test_handler decision).
Proof. split; [exact hidden_choice_not_mdp_state|exact request_sample_reply_stays_mdp]. Qed.

(** A many-to-one VALUE map, independently of the event permutation.
    Totality transport does not assume injectivity of mapped heads. *)
Example collapsed_successors_total :
  @sem_total MF FI FO unit (free_omega_bind hidden_front (fun _ => FORet tt)).
Proof.
  apply subenum_free_omega_total_map.
  apply fair_heads_total.
Qed.

Example interpreted_fragment_coincidence b :
  (W (PTree.interp mdp_test_handler (Tau (service b)))
     (PTree.interp mdp_test_handler (service b)) <->
   TB (PTree.interp mdp_test_handler (Tau (service b)))
      (PTree.interp mdp_test_handler (service b))).
Proof.
  apply (subenum_mdp_interp_peutt_tree_trans_iff mdp_test_atomic).
  - apply (proj2 (mdp_state_tau_iff (FI := FI) (FO := FO) _)).
    apply infinite_service_mdp.
  - apply infinite_service_mdp.
Qed.

(** Starts with independently constructed TRANSITION evidence, transports
    it by stage 3, and recovers peutt at the preserved MDP target. *)
Example transition_route_recovers_peutt b :
  W (PTree.interp mdp_test_handler (Tau (service b)))
    (PTree.interp mdp_test_handler (service b)).
Proof.
  apply (subenum_mdp_interp_transition_to_peutt mdp_test_atomic).
  - apply (proj2 (mdp_state_tau_iff (FI := FI) (FO := FO) _)).
    apply infinite_service_mdp.
  - apply infinite_service_mdp.
  - apply delay_transition_bisim.
Qed.

(** The other route uses guarded peutt preservation and the same fragment
    contract; it does not invoke stage 3's transition preservation. *)
Example guarded_route_preserves_transition b :
  TB (PTree.interp mdp_test_handler (Tau (service b)))
     (PTree.interp mdp_test_handler (service b)).
Proof.
  apply (mdp_guarded_interp_tree_trans
    (subenum_atomic_handler_mdp mdp_test_atomic)
    (atomic_handler_guarded mdp_test_atomic)).
  - apply (proj2 (mdp_state_tau_iff (FI := FI) (FO := FO) _)).
    apply infinite_service_mdp.
  - apply infinite_service_mdp.
  - apply delay_transition_bisim.
Qed.
