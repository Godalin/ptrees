(** Canonical completion specialization of generic MDP reflection. The
    optional native joint-realization law, NOT the choice of SubEnumQ,
    discharges the mapped-lifting reflection obligation. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure
  PTree.Prob.FreeOmega.NativeCoupling PTree.Prob.FreeOmega.StructuralMeasure.
From PTree.Eq Require Import PEutt.
From PTree.Semantics Require Import MDPEmbedding MDPReflection HeadTransition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Reflection.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NJ : @FreeOmegaNativeCouplingLaws MN NI NO}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (@FreeOmegaObservableSemanticOmega MN NI NO).
Variable D : MDP MN.
Local Notation E := (mdpE (mdp_observations D) (mdp_actions D)).

Theorem free_mdp_peutt_iff s t :
  mdp_bisim (D := D) s t <->
  @peutt E MN MF FI FC FreeOmegaMixedMeasure FO unit unit eq
    (mdp_encode s) (mdp_encode t).
Proof.
  exact (mdp_peutt_iff (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    (FD := free_omega_observable_dirac_ae_laws)
    (@free_omega_sampled_heads_reflect MN NI NC NCAE NO NJ) (D := D) s t).
Qed.

Theorem free_mdp_head_bisim_iff s t :
  mdp_bisim (D := D) s t <->
  @head_bisim E MN MF FI FC FreeOmegaMixedMeasure FO unit unit eq
    (mdp_encode_head s) (mdp_encode_head t).
Proof.
  exact (mdp_head_bisim_iff (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)
    (@free_omega_sampled_heads_reflect MN NI NC NCAE NO NJ) (D := D) s t).
Qed.
End Reflection.
