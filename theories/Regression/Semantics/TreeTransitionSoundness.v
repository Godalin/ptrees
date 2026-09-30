(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Semantics Require Import TreeTransition TreeTransitionBisim.
Fail Check PTree.Eq.PEutt.peutt.
(** Only the explicit comparison layer crosses this import boundary. *)
From PTree.Eq Require Import PEutt.
From PTree.Semantics Require Import TreeTransitionSoundness.
From PTree.Regression.Semantics Require Import TreeTransition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega
  SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation W := (@peutt rawE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool eq).
Local Notation TB := (@trans_bisim rawE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool eq).

(** Exercise the comparison at a probability mixture, not just Ret/Vis. *)
Lemma delayed_mixture_peutt : W (Tau mixture) mixture.
Proof. apply peutt_tau_l. Qed.

Example delayed_mixture_transition_bisim : TB (Tau mixture) mixture.
Proof. exact (peutt_trans_bisim (FI := FI) (FC := FC) (FO := FO) (RR := eq) delayed_mixture_peutt). Qed.

(** The extracted action coupling keeps the previously checked half-mass
    result. Neither the endpoint nor inclusion normalizes the output. *)
Example delayed_mixture_action_coupling :
  @sem_lift MF FI _ _ (trans_head_rel W) mixed_out mixed_out.
Proof.
  exact (peutt_preserves_trans (FI := FI) (FC := FC) (FO := FO) (RR := eq) delayed_mixture_peutt
    delayed_mixture_same_transition mixture_action_weighted_sum).
Qed.

(** Arbitrary relations on the common return type are supported, rather
    than silently baking equality into the comparison theorem. *)
Example related_returns_transition_bisim :
  @trans_bisim rawE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool
    (fun x y => x = negb y) (Ret true) (Ret false).
Proof.
  assert (Hret : @peutt rawE SubEnumQ MF FI FC FreeOmegaMixedMeasure FO bool bool
    (fun x y => x = negb y) (Ret true) (Ret false)).
  { apply peutt_ret. reflexivity. }
  exact (peutt_trans_bisim (FI := FI) (FC := FC) (FO := FO) Hret).
Qed.
