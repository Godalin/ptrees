(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Automatic Proposition Inductives.

From PTree.Eq Require Import StableHittingRelation.
From Coq.Program Require Import Equality.
From Coq Require Import RelationClasses.
From Coq.Logic Require Import ClassicalDescription.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Representation.
From PTree.Eq.Internal Require Import FiniteInternal FiniteInternalHitting.
From PTree.Eq Require Import PStrong PEutt.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalAcceleration.
From PTree.Examples Require Import RandomWalk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ.

Variant residualE : Type -> Type := .
(** Purely internal, potentially unbounded retry: there is no Vis guard
    between retries.  Each failed toss has one administrative Tau on the
    left and two on the right. *)
CoFixpoint residual_retry_left : ptree residualE SubEnumQ bool :=
  Prob rw_coin (fun b : bool => if b then Ret true else Tau residual_retry_left).

CoFixpoint residual_retry_right : ptree residualE SubEnumQ bool :=
  Prob rw_coin (fun b : bool => if b then Ret true else Tau (Tau residual_retry_right)).

(** Select only the explicit administrative prefixes.  Propositional
    equality avoids assuming an eta law or dependent elimination for the
    coinductive tree.  These are proof witnesses, not executable samplers. *)
Definition residual_retry_cut1 (t : ptree residualE SubEnumQ bool) :
    FreeOmega SubEnumQ (ptree residualE SubEnumQ bool) :=
  if excluded_middle_informative (t = Tau residual_retry_left)
  then FORet residual_retry_left else FORet t.

Definition residual_retry_cut2 (t : ptree residualE SubEnumQ bool) :
    FreeOmega SubEnumQ (ptree residualE SubEnumQ bool) :=
  if excluded_middle_informative (t = Tau (Tau residual_retry_right))
  then FORet residual_retry_right else FORet t.

Local Notation SFI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Lemma residual_retry_cut1_valid t :
  @finite_internal residualE SubEnumQ (FreeOmega SubEnumQ) SFI FreeOmegaMixedMeasure
    bool t (residual_retry_cut1 t).
Proof.
  unfold residual_retry_cut1. destruct (excluded_middle_informative _) as [->|Hne].
  - apply FITau. exact (@FIStop residualE SubEnumQ (FreeOmega SubEnumQ) SFI
      FreeOmegaMixedMeasure bool _).
  - exact (@FIStop residualE SubEnumQ (FreeOmega SubEnumQ) SFI
      FreeOmegaMixedMeasure bool _).
Qed.

Lemma residual_retry_cut2_valid t :
  @finite_internal residualE SubEnumQ (FreeOmega SubEnumQ) SFI FreeOmegaMixedMeasure
    bool t (residual_retry_cut2 t).
Proof.
  unfold residual_retry_cut2. destruct (excluded_middle_informative _) as [->|Hne].
  - apply FITau. apply FITau.
    exact (@FIStop residualE SubEnumQ (FreeOmega SubEnumQ) SFI
      FreeOmegaMixedMeasure bool _).
  - exact (@FIStop residualE SubEnumQ (FreeOmega SubEnumQ) SFI
      FreeOmegaMixedMeasure bool _).
Qed.

Inductive residual_retry_pairs :
    ptree residualE SubEnumQ bool -> ptree residualE SubEnumQ bool -> Prop :=
| ResidualRetryReturn : residual_retry_pairs (Ret true) (Ret true)
| ResidualRetryLoop : residual_retry_pairs residual_retry_left residual_retry_right
| ResidualRetryDelay : residual_retry_pairs
    (Tau residual_retry_left) (Tau (Tau residual_retry_right)).

Lemma residual_retry_cuts_structural t1 t2 :
  residual_retry_pairs t1 t2 ->
  free_omega_lift (fun t u => pstrongF eq residual_retry_pairs (observe t) (observe u))
    (residual_retry_cut1 t1) (residual_retry_cut2 t2).
Proof.
  intro Hpair. destruct Hpair;
    unfold residual_retry_cut1, residual_retry_cut2;
    destruct (excluded_middle_informative _) as [H1|H1];
    destruct (excluded_middle_informative _) as [H2|H2].
  all: try solve [exfalso; apply H1; reflexivity | exfalso; apply H2; reflexivity].
  all: try solve [apply (f_equal (@observe residualE SubEnumQ bool)) in H1; discriminate H1
    | apply (f_equal (@observe residualE SubEnumQ bool)) in H2; discriminate H2].
  all: apply FOLRet; unfold observe; cbn.
  - constructor. reflexivity.
  - constructor. apply sem_lift_refl. intros []; constructor.
  - constructor. apply sem_lift_refl. intros []; constructor.
Qed.

Lemma residual_retry_cuts_coupled t1 t2 :
  residual_retry_pairs t1 t2 ->
  free_omega_qlift (fun t u => pstrongF eq residual_retry_pairs (observe t) (observe u))
    (residual_retry_cut1 t1) (residual_retry_cut2 t2).
Proof. intro Hpair. apply FOQLStructural, residual_retry_cuts_structural, Hpair. Qed.

Lemma residual_retries_peutt :
  @peutt residualE SubEnumQ (FreeOmega SubEnumQ) SFI
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    residual_retry_left residual_retry_right.
Proof.
  eapply peutt_coinduction_finite_internal_policies with
    (sim := residual_retry_pairs)
    (cut1 := residual_retry_cut1) (cut2 := residual_retry_cut2).
  - apply residual_retry_cut1_valid.
  - apply residual_retry_cut2_valid.
  - apply residual_retry_cuts_coupled.
  - constructor.
Qed.

(** Infinitely many visible rounds, each with a finite administrative delay.
    This exercises the native hitting up-to rule: the coinductive guard
    is the visible head, not an administrative internal step. *)
Variant residual_tickE : Type -> Type := ResidualTick : residual_tickE unit.

CoFixpoint residual_service_left : ptree residual_tickE SubEnumQ bool :=
  Vis ResidualTick (fun _ => Tau residual_service_left).

CoFixpoint residual_service_right : ptree residual_tickE SubEnumQ bool :=
  Vis ResidualTick (fun _ => Tau (Tau residual_service_right)).

Lemma residual_services_peutt :
  @peutt residual_tickE SubEnumQ (FreeOmega SubEnumQ)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool bool eq
    residual_service_left residual_service_right.
Proof.
  eapply peutt_coinduction_upto_finite_internal with
    (sim := fun s1 s2 =>
      s1 = observe residual_service_left /\ s2 = observe residual_service_right).
  - intros s1 s2 [-> ->].
    apply stable_hitting_match_vis. intros [].
    exists (Tau residual_service_left), (Tau (Tau residual_service_right)),
      (FORet residual_service_left), (FORet residual_service_right).
    split; [reflexivity|]. split; [reflexivity|].
    split.
    + apply FITau. exact (@FIStop residual_tickE SubEnumQ (FreeOmega SubEnumQ)
        (FreeOmegaObservableSemanticMeasure
          (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
        FreeOmegaMixedMeasure bool residual_service_left).
    + split.
      * apply FITau. apply FITau.
        exact (@FIStop residual_tickE SubEnumQ (FreeOmega SubEnumQ)
          (FreeOmegaObservableSemanticMeasure
            (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
          FreeOmegaMixedMeasure bool residual_service_right).
      * apply FOQLStructural. apply FOLRet. split; reflexivity.
  - split; reflexivity.
Qed.
