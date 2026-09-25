(** Atomic MDP preservation consumes only probability laws and the generic
    atomic certificate. Totality of the value-map is an explicit local
    measure obligation, not a premise asserting interpreter preservation. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed BindOrder.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Interp Require Import Atomic MDP.
From PTree.Semantics Require Import MDPFragment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section AtomicMDPInterp.
Context {E MN MF : Type -> Type}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{FK : @SemanticMeasureAEKleisliLaws MF FI}
  `{FCAE : @SemanticMeasureCouplingAELaws MF FI}
  `{MX : MixedMeasure MN MF} `{FO : @SemanticOmega MF FI}
  `{Ord : @SemanticMeasureOrderLaws MF FI FO}
  `{Omega : @SemanticOmegaLaws MF FI FO}
  `{Cofinal : @SemanticOmegaCofinalityLaws MF FI FO}
  `{Diagonal : @SemanticMeasureDiagonalLaws MF FI FO}
  `{BindOrd : @SemanticMeasureBindOrderLaws MF FI FO}
  `{MixedOrd : @MixedMeasureBindOrderLaws MN MF FI MX FO}
  `{Directed : @SemanticOmegaDirectedCofinalityLaws MF FI FO}
  `{Select : @SemanticOmegaSelection MF FI FO}
  `{FOAE : @SemanticOmegaAELaws MF FI FO}.
(** Output extensionality is an explicit local probability premise rather
    than a new class. It does not mention trees or interpretation. *)
Hypothesis Hlimit : forall A (c : nat -> MF A) mu nu,
  sem_eq mu nu -> sem_lub c mu -> sem_lub c nu.
Variable handler : forall X, E X -> ptree E MN X.
Context {R : Type}.
Local Notation head := (stable_head E MN R).
Local Notation good := (@mdp_head E MN MF FI FC MX FO R).
Local Notation state := (@mdp_state E MN MF FI FC MX FO R).
Variable atom : atomic_handler (MF := MF) handler.

(** This is a measure-side mapping obligation, not a preservation premise.
    [sem_total_proper] alone does not imply it. The SubEnumQ specialization
    proves it for all maps, not merely this handler's head map. *)
Hypothesis Htotal_map : forall mu : MF head,
  @sem_total MF FI FO _ mu ->
  @sem_total MF FI FO _ (atomic_map atom mu).

Definition mdp_atomic_candidate (h : head) : Prop :=
  exists source, good source /\ h = atomic_head atom source.

Lemma mdp_atomic_candidate_postfixed h :
  mdp_atomic_candidate h ->
  @mdp_headF E MN MF FI MX FO R mdp_atomic_candidate h.
Proof.
  intros [source [Hgood ->]]. destruct source as [r|X e k]; [exact I|].
  intro x. destruct (proj1 (mdp_head_vis_iff e k) Hgood x)
    as [mu [Hhit [Htotal Hae]]].
  exists (atomic_map atom mu). split.
  - constructor. apply (atomic_finish_bind Hlimit). apply (atomic_interp_hitting Hlimit). exact Hhit.
  - split; [apply Htotal_map; exact Htotal|].
    unfold atomic_map. eapply sem_ae_bind; [exact Hae|].
    intros source Hsource. apply sem_ae_ret. exists source. auto.
Qed.

Theorem mdp_head_atomic h : good h -> good (atomic_head atom h).
Proof.
  intro Hh. eapply mdp_head_coinduction with (P := mdp_atomic_candidate).
  - exact mdp_atomic_candidate_postfixed.
  - exists h. auto.
Qed.

Theorem atomic_handler_mdp : mdp_handler (R := R) handler.
Proof.
  intros h Hh. eapply mdp_state_of_hitting with
    (h := atomic_head atom h) (out := sem_ret (atomic_head atom h)).
  - apply (atomic_interp_head_hitting Hlimit).
  - apply (sem_eq_refl (SI := FI)).
  - apply mdp_head_atomic. exact Hh.
Qed.

Theorem mdp_state_interp_atomic t : state t -> state (PTree.interp handler t).
Proof. exact (mdp_state_interp (FI := FI) (FO := FO) (MX := MX)
  atomic_handler_mdp (t := t)). Qed.

End AtomicMDPInterp.
