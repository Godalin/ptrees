(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnum.FreeOmega.Total.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Bind.
From PTree.Interp.FreeOmega Require Import Guarded.
From PTree.Semantics Require Import MDPFragment.
From PTree.Interp.FreeOmega Require Import Atomic MDP.
From PTree.Interp.Backend Require Import SubEnum.
From PTree.Semantics Require Import TreeTransition TreeTransitionBisim.
From PTree.Regression.Semantics Require Import MDPFragment MDPCoincidence AtomicInterp.
Require Import PTree.Interp.Kernel.
From PTree.Interp.FreeOmega Require Import Cofinality.
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

Section HeterogeneousEffects.

(** Genuinely different inductive families, not aliases or permutations
    of one signature. AtomicInterp's E -> E certificate is not used. *)
Variant sourceE : Type -> Type :=
| AskS : sourceE bool | ReplyS : bool -> sourceE unit.
Variant targetE : Type -> Type :=
| AskT : targetE bool | ReplyT : bool -> targetE unit.

Definition hetero_event X (e : sourceE X) : targetE X :=
  match e in sourceE X return targetE X with
  | AskS => AskT | ReplyS b => ReplyT (negb b)
  end.
Definition hetero_handler X (e : sourceE X) : ptree targetE SubEnum X :=
  Tau (Vis (hetero_event e) (fun x => Ret x)).

Lemma hetero_handler_guarded : guarded_handler
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega) hetero_handler.
Proof.
  apply (guarded_handler_of_hitting
    (NI := SubEnum_SemanticMeasure) (NC := SubEnum_SemanticMeasureCoreLaws)
    (NO := SubEnum_SemanticOmega) (NCAE := SubEnum_SemanticMeasureCouplingAELaws)
    (NCount := SubEnum_SemanticMeasureCountableAELaws)).
  intros X e. exists (FORet (FHVis (hetero_event e) (fun x => Ret x))).
  split.
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
  - constructor. exact I.
Qed.

Section ReturnCarrier.
Context {R : Type}.
Local Notation SH := (stable_head sourceE SubEnum R).
Local Notation TH := (stable_head targetE SubEnum R).
Local Notation SG := (@mdp_head sourceE SubEnum MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation TG := (@mdp_head targetE SubEnum MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation SS := (@mdp_state sourceE SubEnum MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation TS := (@mdp_state targetE SubEnum MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation shits t out := (@ptree_stable_hitting sourceE SubEnum MF FI
  FreeOmegaMixedMeasure FO R (observe t) out).
Local Notation thits t out := (@ptree_stable_hitting targetE SubEnum MF FI
  FreeOmegaMixedMeasure FO R (observe t) out).

Definition hetero_head (h : SH) : TH :=
  match h with
  | FHRet r => FHRet r
  | @FHVis _ _ _ X e k => FHVis (hetero_event e)
      (fun x => PTree.bind (Ret x) (fun a => PTree.interp hetero_handler (k a)))
  end.
Definition hetero_map (mu : MF SH) : MF TH :=
  free_omega_bind mu (fun h => FORet (hetero_head h)).

Lemma hetero_head_hitting h :
  thits (ptree_interp_head_tree hetero_handler h) (FORet (hetero_head h)).
Proof.
  destruct h as [r|X e k].
  - apply (ptree_stable_hitting_ret (FI := FI) (FO := FO)).
  - destruct (stable_hitting_front_choice (FI := FI) (FO := FO)
      (fun x => PTree.interp hetero_handler (k x))) as [front Hfront].
    apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
    change (thits (PTree.bind (hetero_handler e)
      (fun x => PTree.interp hetero_handler (k x)))
      (sem_bind (FORet (FHVis (hetero_event e) (fun x => Ret x)))
        (stable_head_bind_front (FI := FI)
          (fun x => PTree.interp hetero_handler (k x)) front))).
    eapply (ptree_stable_hitting_bind (FI := FI) (FO := FO)).
    + apply ptree_bind_cofinal_all.
    + apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI) (FO := FO) _ _)).
      apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
    + exact Hfront.
Qed.

Lemma hetero_interp_hitting t mu :
  shits t mu -> thits (PTree.interp hetero_handler t) (hetero_map mu).
Proof.
  intro Hhit. eapply (ptree_stable_hitting_interp (FI := FI) (FO := FO));
    [apply ptree_interp_cofinal_all|exact Hhit|apply hetero_head_hitting].
Qed.

(** Independently discharge the heterogeneous contract for ALL qualifying
    source heads, including heads with non-Dirac probabilistic successors. *)
Lemma hetero_head_mdp h : SG h -> TG (hetero_head h).
Proof.
  intro Hh. eapply mdp_head_coinduction with
    (P := fun target => exists source, SG source /\ target = hetero_head source).
  - intros target [source [Hgood ->]]. destruct source as [r|X e k]; [exact I|].
    intro x. destruct (proj1 (mdp_head_vis_iff e k) Hgood x)
      as [mu [Hhit [Htotal Hae]]].
    exists (hetero_map mu). split.
    + constructor. change (thits (PTree.interp hetero_handler (k x)) (hetero_map mu)).
      apply hetero_interp_hitting. exact Hhit.
    + split.
      * exact (subenum_free_omega_total_map hetero_head Htotal).
      * unfold hetero_map. eapply (free_omega_ae_bind (NI := SubEnum_SemanticMeasure));
          [exact Hae|].
        intros source Hsource. constructor. exists source. auto.
  - exists h. auto.
Qed.

Theorem hetero_handler_mdp : mdp_handler
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega) (R := R) hetero_handler.
Proof.
  intros h Hh. eapply mdp_state_of_hitting with
    (h := hetero_head h) (out := FORet (hetero_head h)).
  - apply hetero_head_hitting.
  - apply (sem_eq_refl (SI := FI)).
  - apply hetero_head_mdp. exact Hh.
Qed.

Theorem heterogeneous_mdp_preservation t : SS t -> TS (PTree.interp hetero_handler t).
Proof. apply mdp_state_interp. exact hetero_handler_mdp. Qed.

Theorem heterogeneous_guarded_transition_preservation t u : SS t -> SS u ->
  @tree_trans_bisim sourceE SubEnum MF FI FC FreeOmegaMixedMeasure FO R R eq t u ->
  @tree_trans_bisim targetE SubEnum MF FI FC FreeOmegaMixedMeasure FO R R eq
    (PTree.interp hetero_handler t) (PTree.interp hetero_handler u).
Proof.
  intros Ht Hu Htu.
  exact (mdp_guarded_interp_tree_trans hetero_handler_mdp hetero_handler_guarded Ht Hu Htu).
Qed.

Theorem heterogeneous_target_coincidence t u : SS t -> SS u ->
  (@peutt targetE SubEnum MF FI FC FreeOmegaMixedMeasure FO R R eq
      (PTree.interp hetero_handler t) (PTree.interp hetero_handler u) <->
   @tree_trans_bisim targetE SubEnum MF FI FC FreeOmegaMixedMeasure FO R R eq
      (PTree.interp hetero_handler t) (PTree.interp hetero_handler u)).
Proof. apply mdp_interp_peutt_tree_trans_iff. exact hetero_handler_mdp. Qed.

(** Independent source transition evidence. This local regression helper
    deliberately uses neither peutt nor its transition-soundness theorem. *)
Lemma hetero_delay_transition_bisim (t : ptree sourceE SubEnum R) :
  @tree_trans_bisim sourceE SubEnum MF FI FC FreeOmegaMixedMeasure FO R R eq (Tau t) t.
Proof.
  eapply tree_trans_bisim_coinduction with
    (sim := fun a b => a = b \/ a = Tau b); [|right; reflexivity].
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
        -- apply sem_lift_refl. intro h. left; reflexivity.
        -- exact (proj2 (tree_trans_tau_iff (FI := FI) (FO := FO) _ _ _) Hout).
        -- apply sem_lift_refl. intro h. left; reflexivity.
Qed.

End ReturnCarrier.

(** An infinite protocol, with distinct source and target event types. *)
CoFixpoint hetero_service : ptree sourceE SubEnum unit :=
  Vis AskS (fun b => Vis (ReplyS b) (fun _ => hetero_service)).
Definition hetero_service_head : stable_head sourceE SubEnum unit :=
  FHVis AskS (fun b => Vis (ReplyS b) (fun _ => hetero_service)).
Definition hetero_reply_head b : stable_head sourceE SubEnum unit :=
  FHVis (ReplyS b) (fun _ => hetero_service).
Local Notation SState := (@mdp_state sourceE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit).
Local Notation TState := (@mdp_state targetE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit).

Lemma hetero_dirac_total (h : stable_head sourceE SubEnum unit) :
  @sem_total MF FI FO _ (FORet h).
Proof.
  apply free_omega_observable_total_intro.
  exists unit, (fun _ => tt), (subenum_ret tt). split; [constructor|].
  native_compute. reflexivity.
Qed.

Lemma hetero_service_mdp : SState hetero_service.
Proof.
  eapply mdp_state_of_hitting with
    (h := hetero_service_head) (out := FORet hetero_service_head).
  - apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
  - apply (sem_eq_refl (SI := FI)).
  - eapply mdp_head_coinduction with
      (P := fun h => h = hetero_service_head \/ exists b, h = hetero_reply_head b).
    + intros h [-> | [b ->]].
      * intro x. exists (FORet (hetero_reply_head x)). split.
        -- constructor. apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
        -- split; [apply hetero_dirac_total|]. constructor. right. exists x. reflexivity.
      * intro x. exists (FORet hetero_service_head). split.
        -- constructor. apply (ptree_stable_hitting_vis (FI := FI) (FO := FO)).
        -- split; [apply hetero_dirac_total|]. constructor. left. reflexivity.
    + left. reflexivity.
Qed.

Example heterogeneous_infinite_service_state :
  TState (PTree.interp hetero_handler hetero_service).
Proof. exact (heterogeneous_mdp_preservation hetero_service_mdp). Qed.

Example heterogeneous_infinite_service_transition :
  @tree_trans_bisim targetE SubEnum MF FI FC FreeOmegaMixedMeasure FO unit unit eq
    (PTree.interp hetero_handler (Tau hetero_service))
    (PTree.interp hetero_handler hetero_service).
Proof.
  apply heterogeneous_guarded_transition_preservation.
  - apply (proj2 (mdp_state_tau_iff (FI := FI) (FO := FO) _)). exact hetero_service_mdp.
  - exact hetero_service_mdp.
  - apply hetero_delay_transition_bisim.
Qed.

Example heterogeneous_reply_label b :
  hetero_handler (ReplyS b) = Tau (Vis (ReplyT (negb b)) (fun x => Ret x)).
Proof. reflexivity. Qed.

End HeterogeneousEffects.
