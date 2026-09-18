Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Automatic Proposition Inductives.

Require Import RelationClasses.
From Coq Require Import Program.Equality.

From PTree.Core Require Import PTreeDefinition PTreeEnum.
From PTree.Prob Require Import DiscreteMC TwoLevelMeasureEnum FreeOmegaMeasure.
From PTree.Eq Require Import PStrong PFinite PEutt PEuttRewrite
  OperationalProbabilisticPTSFreeOmega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

Variant hierarchyE : Type -> Type := .
Local Notation MF := (FreeOmega Enum).

(** A finite weak step removes one Tau even when the remaining computation
    has no stable observation.  Thus "finite" describes the compressed
    prefix, not global termination. *)
CoFixpoint hierarchy_spin : ptree hierarchyE Enum bool := Tau hierarchy_spin.

Lemma pfinite_tau_before_divergence :
  @pfinite hierarchyE Enum MF Enum_SemanticMeasure
    Enum_SemanticMeasureCoreLaws
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
    bool bool eq (Tau hierarchy_spin) hierarchy_spin.
Proof. apply pfinite_tau_l. Qed.

Lemma tau_ret_not_pstrong :
  ~ @pstrong hierarchyE Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws bool bool eq
      (Tau (Ret true)) (Ret true).
Proof.
  intro H. apply pstrong_unfold in H. dependent destruction H.
Qed.

Lemma tau_ret_pfinite :
  @pfinite hierarchyE Enum MF Enum_SemanticMeasure
    Enum_SemanticMeasureCoreLaws
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
    bool bool eq (Tau (Ret true)) (Ret true).
Proof. apply pfinite_tau_l. Qed.

Lemma pfinite_promotes_to_peutt :
  @peutt hierarchyE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
    bool bool eq (Tau (Ret true)) (Ret true).
Proof. apply free_peutt_of_pfinite. exact tau_ret_pfinite. Qed.

(** Generic endpoint rewriting consumes the native [subrelation] instance;
    it is not specialized to [pfinite]. *)
Lemma pfinite_endpoint_rewrite (t : ptree hierarchyE Enum bool) :
  @peutt hierarchyE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
    bool bool eq (Tau t) t.
Proof.
  eapply peutt_rewrite_l
    with (R := @pfinite hierarchyE Enum MF Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws
      (FreeOmegaObservableSemanticMeasure
        (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
      bool bool eq).
  - apply free_pfinite_peutt_subrelation.
  - apply pfinite_tau_l.
  - apply peutt_refl.
Qed.
