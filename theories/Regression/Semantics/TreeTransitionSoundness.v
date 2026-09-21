(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.Enum.Measure PTree.Prob.Backend.Enum.Representation.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Semantics Require Import TreeTransition TreeTransitionBisim.
Fail Check PTree.Eq.PEutt.peutt.
(** Only the explicit comparison layer crosses this import boundary. *)
From PTree.Eq Require Import PEutt.
From PTree.Semantics Require Import TreeTransitionSoundness.
From PTree.Regression.Semantics Require Import TreeTransition.
From PTree.Examples.InteractiveVonNeumann Require Import InteractiveVonNeumannService.
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
Local Notation W := (@peutt rawE SubEnum MF FI FC FreeOmegaMixedMeasure FO bool bool eq).
Local Notation TB := (@tree_trans_bisim rawE SubEnum MF FI FC FreeOmegaMixedMeasure FO bool bool eq).

(** Exercise the comparison at a probability mixture, not just Ret/Vis. *)
Lemma delayed_mixture_peutt : W (Tau mixture) mixture.
Proof. apply peutt_tau_l. Qed.

Example delayed_mixture_transition_bisim : TB (Tau mixture) mixture.
Proof. exact (peutt_tree_trans_bisim (FI := FI) (FC := FC) (FO := FO) (RR := eq) delayed_mixture_peutt). Qed.

Example delayed_mixture_postfixed :
  @tree_trans_bisimF rawE SubEnum MF FI FreeOmegaMixedMeasure FO bool bool eq
    W (Tau mixture) mixture.
Proof. exact (peutt_tree_trans_postfixed (FI := FI) (FC := FC) (FO := FO) (RR := eq) delayed_mixture_peutt). Qed.

(** The extracted action coupling keeps the previously checked half-mass
    result. Neither the endpoint nor inclusion normalizes the output. *)
Example delayed_mixture_action_coupling :
  @sem_lift MF FI _ _ (tree_trans_head_rel W) mixed_out mixed_out.
Proof.
  exact (peutt_preserves_tree_trans (FI := FI) (FC := FC) (FO := FO) (RR := eq) delayed_mixture_peutt
    delayed_mixture_same_transition mixture_action_weighted_sum).
Qed.

(** Arbitrary relations on the common return type are supported, rather
    than silently baking equality into the comparison theorem. *)
Example related_returns_transition_bisim :
  @tree_trans_bisim rawE SubEnum MF FI FC FreeOmegaMixedMeasure FO bool bool
    (fun x y => x = negb y) (Ret true) (Ret false).
Proof.
  assert (Hret : @peutt rawE SubEnum MF FI FC FreeOmegaMixedMeasure FO bool bool
    (fun x y => x = negb y) (Ret true) (Ret false)).
  { apply peutt_ret. reflexivity. }
  exact (peutt_tree_trans_bisim (FI := FI) (FC := FC) (FO := FO) Hret).
Qed.

(** Reuse the existing infinite interaction / unbounded internal-retry
    theorem as a client. No MDP coincidence or converse is invoked. The
    existing service uses Enum/FreeOmega; the tests above use SubEnum. *)
Theorem interactive_von_neumann_service_transition_bisim :
  @tree_trans_bisim coin_serviceE Enum.Enum (FreeOmega Enum.Enum)
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    von_neumann_service direct_fair_service.
Proof.
  exact (peutt_tree_trans_bisim
    (FI := FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    (FO := @FreeOmegaObservableSemanticOmega Enum.Enum Enum_SemanticMeasure Enum_SemanticOmega)
    (RR := eq) interactive_von_neumann_service_equivalent).
Qed.
