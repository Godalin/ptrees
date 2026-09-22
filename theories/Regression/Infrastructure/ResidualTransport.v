(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Classes Require Import RelationClasses.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PStrong PEutt.
From PTree.Regression.Infrastructure Require Import ResidualFinite.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

(** The three-pair relation is not an equivalence relation on trees.
    It is not exposed as another equivalence on programs. *)
Lemma retry_pairs_not_reflexive : ~ Reflexive residual_retry_pairs.
Proof.
  intro H. specialize (H (Ret false)). inversion H.
  all: match goal with
    | Heq : Ret false = _ |- _ =>
        apply (f_equal (@observe residualE SubEnumQ bool)) in Heq; discriminate Heq
    | Heq : _ = Ret false |- _ =>
        apply (f_equal (@observe residualE SubEnumQ bool)) in Heq; discriminate Heq
    end.
Qed.

(** The candidate is only a local classification of program pairs.
    Its behavioral conclusion follows from the already proved complete
    hitting comparison and Tau transparency; no auxiliary GFP is used. *)
Theorem retry_pairs_peutt_without_equivalence t u :
  residual_retry_pairs t u ->
  @peutt residualE SubEnumQ MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool bool eq t u.
Proof.
  intro H. destruct H.
  - apply peutt_refl.
  - apply residual_retries_peutt.
  - eapply peutt_trans; [apply peutt_tau_l|].
    eapply peutt_trans; [apply residual_retries_peutt|].
    apply peutt_sym. eapply peutt_trans; apply peutt_tau_l.
Qed.
