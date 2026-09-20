(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Classes Require Import RelationClasses.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PStrong PEutt.
From PTree.Regression.Infrastructure Require Import ResidualFinite.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

(** The three-pair relation is not an equivalence relation on trees.
    It is not exposed as another equivalence on programs. *)
Lemma retry_pairs_not_reflexive : ~ Reflexive residual_retry_pairs.
Proof.
  intro H. specialize (H (Ret false)). inversion H.
  all: match goal with
    | Heq : Ret false = _ |- _ =>
        apply (f_equal (@observe residualE SubEnum bool)) in Heq; discriminate Heq
    | Heq : _ = Ret false |- _ =>
        apply (f_equal (@observe residualE SubEnum bool)) in Heq; discriminate Heq
    end.
Qed.

(** The candidate is only a local classification of program pairs.
    Its behavioral conclusion follows from the already proved complete
    hitting comparison and Tau transparency; no auxiliary GFP is used. *)
Theorem retry_pairs_peutt_without_equivalence t u :
  residual_retry_pairs t u ->
  @peutt residualE SubEnum MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool bool eq t u.
Proof.
  intro H. destruct H.
  - apply peutt_refl.
  - apply residual_retries_peutt.
  - eapply peutt_trans; [apply peutt_tau_l|].
    eapply peutt_trans; [apply residual_retries_peutt|].
    apply peutt_sym. eapply peutt_trans; apply peutt_tau_l.
Qed.
