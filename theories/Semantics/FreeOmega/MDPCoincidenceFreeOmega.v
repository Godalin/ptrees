(** Role: Comparison semantics. Depends on canonical theory; not the canonical peutt relation or interpreter theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import PEutt.
From PTree.Semantics Require Import MDPFragment TreeTransitionBisim MDPCoincidence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A proof of an existing capability, not a new axiom or global instance.
    This fact is structural in FreeOmega and needs no node separation law. *)
Lemma free_omega_observable_dirac_ae_laws {MN}
    `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI} :
  @SemanticMeasureDiracAELaws (FreeOmega MN)
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Proof.
  constructor. intros A x P. split; intro H.
  - change (free_omega_ae P (FORet x)) in H. dependent destruction H. assumption.
  - apply FOAERet. exact H.
Qed.

Section FreeOmegaCoincidence.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.
Context {E : Type -> Type} {R : Type}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega MN NI NO).
Local Notation state := (@mdp_state E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO R).

(** No hidden separation premise remains at this endpoint. Both canonical
    native backends can supply these existing node capabilities. *)
Theorem free_mdp_state_tree_trans_bisim_peutt (t u : ptree E MN R) :
  state t -> state u ->
  @tree_trans_bisim E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO R R eq t u ->
  @peutt E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO R R eq t u.
Proof.
  apply (mdp_state_tree_trans_bisim_peutt (FI := FI) (FC := FC) (FO := FO)
    (FD := free_omega_observable_dirac_ae_laws)).
Qed.

Theorem free_mdp_state_peutt_tree_trans_iff (t u : ptree E MN R) :
  state t -> state u ->
  (@peutt E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO R R eq t u <->
   @tree_trans_bisim E MN (FreeOmega MN) FI FC FreeOmegaMixedMeasure FO R R eq t u).
Proof.
  apply (mdp_state_peutt_tree_trans_iff (FI := FI) (FC := FC) (FO := FO)
    (FD := free_omega_observable_dirac_ae_laws)).
Qed.
End FreeOmegaCoincidence.
