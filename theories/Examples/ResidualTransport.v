Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Classes.RelationClasses.
From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure.
From PTree.Eq Require Import FiniteInternal PFiniteResidual PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternalTransportSubEnum.
From PTree.Examples Require Import ResidualFinite.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

(** The three-pair relation is not an equivalence relation on trees.
    The new rule requires only its ordinary postfixedness. *)
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

Lemma retry_pairs_postfixed t u : residual_retry_pairs t u ->
  @pfinite_residualF residualE SubEnum MF SubEnum_SemanticMeasure FI
    FreeOmegaMixedMeasure bool bool eq residual_retry_pairs t u.
Proof.
  intro H. destruct H.
  - eapply PFiniteResidualStep; [apply FIStop|apply FIStop|].
    apply sem_lift_ret. unfold pfinite_guard, observe; cbn. constructor. reflexivity.
  - eapply PFiniteResidualStep; [apply FIStop|apply FIStop|].
    apply sem_lift_ret. unfold pfinite_guard, observe; cbn. constructor.
    apply sem_lift_refl. intros []; constructor.
  - eapply PFiniteResidualStep.
    + apply FITau, FIStop.
    + apply FITau, FITau, FIStop.
    + apply sem_lift_ret. unfold pfinite_guard, observe; cbn. constructor.
      apply sem_lift_refl. intros []; constructor.
Qed.

Lemma retry_pairs_residual : forall t u, residual_retry_pairs t u ->
  @pfinite_residual_rel residualE SubEnum MF
    SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws FI
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure bool bool eq t u.
Proof.
  unfold pfinite_residual_rel. coinduction CH CIH.
  intros t u Hpair. eapply pfinite_residualF_monotone.
  - intros x y Hxy. exact (CIH x y Hxy).
  - exact (retry_pairs_postfixed Hpair).
Qed.

Theorem retry_pairs_peutt_without_equivalence t u :
  residual_retry_pairs t u ->
  @peutt residualE SubEnum MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool bool eq t u.
Proof.
  intro H. apply pfinite_residual_rel_peutt_subenum, retry_pairs_residual, H.
Qed.

(** A client of the raw GFP theorem has no equivalence, AST, joint-row,
    or numerical-model premise, including at heterogeneous result types. *)
Example heterogeneous_residual_sound {E : Type -> Type} (RR : nat -> bool -> Prop)
    (t : ptree E SubEnum nat) (u : ptree E SubEnum bool) :
  @pfinite_residual_rel E SubEnum MF SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
    FI FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure nat bool RR t u ->
  @peutt E SubEnum MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega nat bool RR t u.
Proof. apply pfinite_residual_rel_peutt_subenum. Qed.
