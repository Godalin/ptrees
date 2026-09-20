Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Bind GuardedInterp.
From PTree.Semantics Require Import MDPFragment AtomicInterp
  TreeTransitionBisim MDPCoincidenceFreeOmega.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MDPInterp.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega MN NI NO).
Variable handler : forall X, E X -> ptree E MN X.
Context {R : Type}.
Local Notation head := (stable_head E MN R).
Local Notation tree := (ptree E MN R).
Local Notation good := (@mdp_head E MN MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation state := (@mdp_state E MN MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation hits t out := (@ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure FO R (observe t) out).

(** A local stable-head contract, not a new interpreter semantics or a
    definition assuming the desired raw-tree preservation theorem. The
    atomic profile below discharges it by unary coinduction. *)
Definition mdp_handler : Prop :=
  forall h : head, good h -> state (ptree_interp_head_tree handler h).

Theorem mdp_state_interp (Hhandler : mdp_handler) (t : tree) :
  state t -> state (PTree.interp handler t).
Proof.
  intros [h [mu [Hhit [Heq Hgood]]]].
  destruct (stable_hitting_front_choice (FI := FI) (FO := FO)
    (fun h : head => ptree_interp_head_tree handler h)) as [front Hfront].
  destruct (Hhandler h Hgood) as [h' [out [Hout [Hdirac Hgood']]]].
  eapply mdp_state_of_hitting with
    (h := h') (out := free_omega_bind mu front).
  - eapply (ptree_stable_hitting_interp (FI := FI) (FO := FO));
      [apply ptree_interp_cofinal_all|exact Hhit|exact Hfront].
  - eapply (sem_eq_trans (SI := FI)) with (y := front h).
    + change (free_omega_qlift eq (free_omega_bind mu front)
        (free_omega_bind (FORet h) front)).
      eapply FOQLBind; [exact Heq|].
      intros a b ->. apply (sem_eq_refl (SI := FI)).
    + eapply (sem_eq_trans (SI := FI)); [|exact Hdirac].
      eapply stable_hitting_unique; [apply Hfront|exact Hout].
  - exact Hgood'.
Qed.

(** Coincidence is reused, not reproved or built into the handler contract.
    No source bisimulation premise is needed for this target-fragment iff. *)
Theorem mdp_interp_peutt_tree_trans_iff (Hhandler : mdp_handler) t u :
  state t -> state u ->
  (@peutt E MN MF FI FC FreeOmegaMixedMeasure FO R R eq
      (PTree.interp handler t) (PTree.interp handler u) <->
   @tree_trans_bisim E MN MF FI FC FreeOmegaMixedMeasure FO R R eq
      (PTree.interp handler t) (PTree.interp handler u)).
Proof.
  intros Ht Hu. apply free_mdp_state_peutt_tree_trans_iff;
    apply mdp_state_interp; assumption.
Qed.

Theorem mdp_guarded_interp_tree_trans (Hhandler : mdp_handler)
    (Hguard : guarded_handler (NI := NI) (NO := NO) handler) t u :
  state t -> state u ->
  @tree_trans_bisim E MN MF FI FC FreeOmegaMixedMeasure FO R R eq t u ->
  @tree_trans_bisim E MN MF FI FC FreeOmegaMixedMeasure FO R R eq
    (PTree.interp handler t) (PTree.interp handler u).
Proof.
  intros Ht Hu Htu.
  apply (proj1 (mdp_interp_peutt_tree_trans_iff Hhandler Ht Hu)).
  apply (peutt_interp_guarded Hguard).
  exact (free_mdp_state_tree_trans_bisim_peutt Ht Hu Htu).
Qed.

Section AtomicProfile.
Variable atom : atomic_handler (NI := NI) (NO := NO) handler.

(** This is a measure-side mapping obligation, not a preservation premise.
    [sem_total_proper] alone does not imply it. The SubEnum specialization
    proves it for all maps, not merely this handler's head map. *)
Hypothesis Htotal_map : forall mu : MF head,
  @sem_total MF FI FO _ mu ->
  @sem_total MF FI FO _ (atomic_map atom mu).

Definition mdp_atomic_candidate (h : head) : Prop :=
  exists source, good source /\ h = atomic_head atom source.

Lemma mdp_atomic_candidate_postfixed h :
  mdp_atomic_candidate h ->
  @mdp_headF E MN MF FI FreeOmegaMixedMeasure FO R mdp_atomic_candidate h.
Proof.
  intros [source [Hgood ->]]. destruct source as [r|X e k]; [exact I|].
  intro x. destruct (proj1 (mdp_head_vis_iff e k) Hgood x)
    as [mu [Hhit [Htotal Hae]]].
  exists (atomic_map atom mu). split.
  - constructor. apply atomic_finish_bind. apply atomic_interp_hitting. exact Hhit.
  - split; [apply Htotal_map; exact Htotal|].
    unfold atomic_map. eapply (free_omega_ae_bind (NI := NI)); [exact Hae|].
    intros source Hsource. constructor. exists source. auto.
Qed.

Theorem mdp_head_atomic h : good h -> good (atomic_head atom h).
Proof.
  intro Hh. eapply mdp_head_coinduction with (P := mdp_atomic_candidate).
  - exact mdp_atomic_candidate_postfixed.
  - exists h. auto.
Qed.

Theorem atomic_handler_mdp : mdp_handler.
Proof.
  intros h Hh. eapply mdp_state_of_hitting with
    (h := atomic_head atom h) (out := FORet (atomic_head atom h)).
  - apply atomic_interp_head_hitting.
  - apply (sem_eq_refl (SI := FI)).
  - apply mdp_head_atomic. exact Hh.
Qed.

Theorem mdp_state_interp_atomic t : state t -> state (PTree.interp handler t).
Proof. apply mdp_state_interp. exact atomic_handler_mdp. Qed.

End AtomicProfile.
End MDPInterp.
