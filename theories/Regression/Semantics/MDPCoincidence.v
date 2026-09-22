(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Semantics Require Import MDPFragment TreeTransition TreeTransitionBisim.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Eq Require Import PEutt.
From PTree.Semantics Require Import MDPCoincidence.
From PTree.Semantics.FreeOmega Require Import MDPCoincidenceFreeOmega.
From PTree.Regression.Semantics Require Import MDPFragment TreeTransitionStrictness.
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
Local Notation tree := (ptree decisionE SubEnum unit).
Local Notation state := (@mdp_state decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit).
Local Notation W := (@peutt decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit unit eq).
Local Notation TB := (@tree_trans_bisim decisionE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit unit eq).

(** Build transition evidence independently, NOT by peutt soundness, so
    the reverse coincidence endpoint is genuinely exercised below. *)
Definition delayed_pair (t u : tree) := t = u \/ t = Tau u.
Lemma delay_transition_bisim (t : tree) : TB (Tau t) t.
Proof.
  eapply tree_trans_bisim_coinduction with (sim := delayed_pair); [|right; reflexivity].
  intros a b [Heq | Heq]; subst a.
  - split.
    + split; intros out Hout; exists out; split; try exact Hout;
        apply sem_lift_refl; intro x; reflexivity.
    + split.
      * split; intros out Hout; exists out; split; try exact Hout;
          apply sem_lift_refl; intro e; reflexivity.
      * intro label. split; intros out Hout; exists out; split; try exact Hout;
          apply sem_lift_refl; intro h; left; reflexivity.
  - split.
    + split; intros out Hout; exists out; split.
      * exact (proj1 (tree_head_observation_tau_iff (FI := FI) (FO := FO) _ _ _) Hout).
      * apply sem_lift_refl. intro r. reflexivity.
      * exact (proj2 (tree_head_observation_tau_iff (FI := FI) (FO := FO) _ _ _) Hout).
      * apply sem_lift_refl. intro r. reflexivity.
    + split.
      * split; intros out Hout; exists out; split.
        -- exact (proj1 (tree_head_observation_tau_iff (FI := FI) (FO := FO) _ _ _) Hout).
        -- apply sem_lift_refl. intro e. reflexivity.
        -- exact (proj2 (tree_head_observation_tau_iff (FI := FI) (FO := FO) _ _ _) Hout).
        -- apply sem_lift_refl. intro e. reflexivity.
      * intro label. split; intros out Hout; exists out; split.
        -- exact (proj1 (tree_trans_tau_iff (FI := FI) (FO := FO) _ _ _) Hout).
        -- apply sem_lift_refl. intro h. left. reflexivity.
        -- exact (proj2 (tree_trans_tau_iff (FI := FI) (FO := FO) _ _ _) Hout).
        -- apply sem_lift_refl. intro h. left. reflexivity.
Qed.

Theorem delayed_decision_peutt_from_transitions : W (Tau decision) decision.
Proof.
  assert (Hstate : state (Tau decision)).
  { apply (proj2 (mdp_state_tau_iff (FI := FI) (FO := FO) _)).
    exact visible_sample_visible_is_mdp. }
  apply (free_mdp_state_tree_trans_bisim_peutt
    (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)
    (t := Tau decision) (u := decision) Hstate visible_sample_visible_is_mdp).
  apply delay_transition_bisim.
Qed.

(** A non-Dirac action continuation is intentionally NOT required to be
    an mdp_state. Its successor distribution is supported on mdp_heads. *)
Example distribution_successor_coincidence :
  ~ state hidden_choice /\
  (W (Tau decision) decision <-> TB (Tau decision) decision).
Proof.
  split; [exact hidden_choice_not_mdp_state|].
  apply (free_mdp_state_peutt_tree_trans_iff
    (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
  - apply (proj2 (mdp_state_tau_iff (FI := FI) (FO := FO) _)).
    exact visible_sample_visible_is_mdp.
  - exact visible_sample_visible_is_mdp.
Qed.

Theorem infinite_service_peutt_from_transitions b : W (Tau (service b)) (service b).
Proof.
  assert (Hstate : state (Tau (service b))).
  { apply (proj2 (mdp_state_tau_iff (FI := FI) (FO := FO) _)).
    apply infinite_service_mdp. }
  apply (free_mdp_state_tree_trans_bisim_peutt
    (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)
    (t := Tau (service b)) (u := service b) Hstate (infinite_service_mdp b)).
  apply delay_transition_bisim.
Qed.

Example terminal_fragment_coincidence : W (Ret tt) (Ret tt) <-> TB (Ret tt) (Ret tt).
Proof.
  apply (free_mdp_state_peutt_tree_trans_iff
    (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega));
    apply (mdp_state_ret (FI := FI) (FO := FO)).
Qed.

(** The accepted strictness pair cannot satisfy both fragment premises.
    This uses the new reverse direction, not an added syntactic restriction. *)
Example strictness_pair_outside_joint_fragment :
  ~ (@mdp_state correlationE SubEnum MF FI FC FreeOmegaMixedMeasure FO bool P /\
     @mdp_state correlationE SubEnum MF FI FC FreeOmegaMixedMeasure FO bool Q).
Proof.
  intros [Hp Hq]. apply correlated_response_not_peutt.
  apply (free_mdp_state_tree_trans_bisim_peutt
    (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega) Hp Hq).
  exact correlated_response_tree_trans_bisim.
Qed.
