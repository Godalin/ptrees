(** Role: Interpreter compositionality. Depends on equational theory (and comparison semantics for Atomic/MDP); not primitive syntax. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import Bind.
From PTree.Interp.FreeOmega Require Import Guarded.
From PTree.Semantics Require Import MDPFragment.
From PTree.Interp.FreeOmega Require Import Atomic.
From PTree.Semantics Require Import TreeTransitionBisim.
From PTree.Semantics.FreeOmega Require Import MDPCoincidenceFreeOmega.
Require Import PTree.Interp.Kernel.
From PTree.Interp.FreeOmega Require Import Cofinality.
Require PTree.Interp.MDP PTree.Interp.MDPAtomic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section GenericMDPInterp.
Context {E F MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega MN NI NO).
Variable handler : forall X, E X -> ptree F MN X.
Context {R : Type}.
Local Notation shead := (stable_head E MN R).
Local Notation tree := (ptree E MN R).
Local Notation sgood := (@mdp_head E MN MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation sstate := (@mdp_state E MN MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation tstate := (@mdp_state F MN MF FI FC FreeOmegaMixedMeasure FO R).

(** A local stable-head contract, not a new interpreter semantics or a
    definition assuming the desired raw-tree preservation theorem. The
    atomic profile below discharges it by unary coinduction. *)
Definition mdp_handler : Prop :=
  @PTree.Interp.MDP.mdp_handler E F MN MF FI FC FreeOmegaMixedMeasure FO handler R.

Local Lemma interp_bind_ret_l A B (x : A) (k : A -> MF B) :
  @sem_eq MF FI _ (sem_bind (sem_ret x) k) (k x).
Proof. apply (sem_eq_refl (SI := FI)). Qed.

Theorem mdp_state_interp (Hhandler : mdp_handler) (t : tree) :
  sstate t -> tstate (PTree.interp handler t).
Proof.
  exact (PTree.Interp.MDP.mdp_state_interp_of_ret_l (FI := FI) (FC := FC)
    (MX := FreeOmegaMixedMeasure) (FO := FO) interp_bind_ret_l Hhandler (t := t)).
Qed.

(** Coincidence is reused, not reproved or built into the handler contract.
    No source bisimulation premise is needed for this target-fragment iff. *)
Theorem mdp_interp_peutt_tree_trans_iff (Hhandler : mdp_handler) t u :
  sstate t -> sstate u ->
  (@peutt F MN MF FI FC FreeOmegaMixedMeasure FO R R eq
      (PTree.interp handler t) (PTree.interp handler u) <->
   @tree_trans_bisim F MN MF FI FC FreeOmegaMixedMeasure FO R R eq
      (PTree.interp handler t) (PTree.interp handler u)).
Proof.
  exact (PTree.Interp.MDP.mdp_interp_peutt_tree_trans_iff
    (FI := FI) (FC := FC) (MX := FreeOmegaMixedMeasure) (FO := FO)
    (FD := free_omega_observable_dirac_ae_laws) Hhandler (t := t) (u := u)).
Qed.

Theorem mdp_guarded_interp_tree_trans (Hhandler : mdp_handler)
    (Hguard : guarded_handler (NI := NI) (NO := NO) handler) t u :
  sstate t -> sstate u ->
  @tree_trans_bisim E MN MF FI FC FreeOmegaMixedMeasure FO R R eq t u ->
  @tree_trans_bisim F MN MF FI FC FreeOmegaMixedMeasure FO R R eq
    (PTree.interp handler t) (PTree.interp handler u).
Proof.
  exact (PTree.Interp.MDP.mdp_guarded_interp_tree_trans
    (FI := FI) (FC := FC) (MX := FreeOmegaMixedMeasure) (FO := FO)
    (FD := free_omega_observable_dirac_ae_laws) Hhandler Hguard (t := t) (u := u)).
Qed.

End GenericMDPInterp.

(** The accepted permutation profile stays homogeneous. No inverse-label
    machinery or atomic-handler statement is generalized here. *)
Section AtomicMDPInterp.
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
Local Notation good := (@mdp_head E MN MF FI FC FreeOmegaMixedMeasure FO R).
Local Notation state := (@mdp_state E MN MF FI FC FreeOmegaMixedMeasure FO R).
Variable atom : atomic_handler (NI := NI) (NO := NO) handler.

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
  @mdp_headF E MN MF FI FreeOmegaMixedMeasure FO R mdp_atomic_candidate h.
Proof.
  exact (PTree.Interp.MDPAtomic.mdp_atomic_candidate_postfixed
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    (@free_omega_observable_lub_limit_proper MN NI NC NO)
    (atom := atomic_generic atom) Htotal_map (h := h)).
Qed.

Theorem mdp_head_atomic h : good h -> good (atomic_head atom h).
Proof.
  exact (PTree.Interp.MDPAtomic.mdp_head_atomic
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    (@free_omega_observable_lub_limit_proper MN NI NC NO)
    (atom := atomic_generic atom) Htotal_map (h := h)).
Qed.

Theorem atomic_handler_mdp : mdp_handler (R := R) handler.
Proof.
  exact (PTree.Interp.MDPAtomic.atomic_handler_mdp
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    (@free_omega_observable_lub_limit_proper MN NI NC NO)
    (atom := atomic_generic atom) Htotal_map ).
Qed.

Theorem mdp_state_interp_atomic t : state t -> state (PTree.interp handler t).
Proof.
  exact (PTree.Interp.MDPAtomic.mdp_state_interp_atomic
    (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    (@free_omega_observable_lub_limit_proper MN NI NC NO)
    (atom := atomic_generic atom) Htotal_map (t := t)).
Qed.

End AtomicMDPInterp.
