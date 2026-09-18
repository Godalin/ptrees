Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Automatic Proposition Inductives.

Require Import RelationClasses.
From Coq Require Import Program.Equality.

From PTree.Core Require Import PTreeDefinition PTreeEnum.
From PTree.Prob Require Import DiscreteMC TwoLevelMeasureEnum FreeOmegaMeasure.
From PTree.Eq Require Import PStruct PStrong PFinite PEutt
  FreeOmega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

Variant hierarchyE : Type -> Type := .
Local Notation MF := (FreeOmega Enum).
Local Notation hierarchy_pfinite :=
  (@pfinite hierarchyE Enum MF Enum_SemanticMeasure
    Enum_SemanticMeasureCoreLaws
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool).

Lemma pfinite_equivalence_regression : Equivalence hierarchy_pfinite.
Proof. exact pfinite_equivalence. Qed.

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
    bool (Tau hierarchy_spin) hierarchy_spin.
Proof. apply pfinite_tau_l. Qed.

Lemma tau_ret_not_pstrong :
  ~ @pstrong hierarchyE Enum Enum_SemanticMeasure
      Enum_SemanticMeasureCoreLaws bool bool eq
      (Tau (Ret true)) (Ret true).
Proof.
  intro H. apply pstrong_unfold in H. dependent destruction H.
Qed.

(** Stopping decomposition is not probability-specific and does not require
    AST.  The first client below stops between two visible interactions;
    the second never reaches its stopping region. *)
Section IterationStoppingRegressions.
Context {E M : Type -> Type}.
Variable tick : E unit.

Definition stopping_source (n : nat) : ptree E M (nat + unit) :=
  match n with
  | O => Ret (inr tt)
  | S m => Vis tick (fun _ => Ret (inl m))
  end.

Definition stopping_prefix (first : bool) : ptree E M (bool + nat) :=
  if first then Vis tick (fun _ => Ret (inl false)) else Ret (inr 1).

Lemma iter_split_eventful_regression :
  pstruct eq (PTree.iter stopping_source 2)
    (PTree.bind (PTree.iter stopping_prefix true) (PTree.iter stopping_source)).
Proof.
  eapply pstruct_iter_split_at with
    (SI := fun (n : nat) (first : bool) => n = if first then 2 else 1)
    (resume := fun n => n).
  - intros n [] ->.
    + right. apply pstruct_fold. cbn. apply PStVis. intros [].
      apply pstruct_fold. cbn. apply PStRet. constructor. reflexivity.
    + left. exists 1. split; reflexivity.
  - reflexivity.
Qed.

Lemma iter_split_unreached_barrier_regression :
  pstruct eq
    (PTree.iter (fun _ : unit => Ret (inl tt) : ptree E M (unit + bool)) tt)
    (PTree.bind
      (PTree.iter (fun _ : unit => Ret (inl tt) : ptree E M (unit + unit)) tt)
      (fun _ => PTree.iter
        (fun _ : unit => Ret (inl tt) : ptree E M (unit + bool)) tt)).
Proof.
  eapply pstruct_iter_split_at with
    (SI := fun (_ _ : unit) => True) (resume := fun _ => tt).
  - intros [] [] _. right. apply pstruct_fold. cbn.
    apply PStRet. constructor. exact I.
  - exact I.
Qed.

End IterationStoppingRegressions.

Lemma tau_ret_pfinite :
  @pfinite hierarchyE Enum MF Enum_SemanticMeasure
    Enum_SemanticMeasureCoreLaws
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
    bool (Tau (Ret true)) (Ret true).
Proof. apply pfinite_tau_l. Qed.

Lemma pfinite_promotes_to_peutt :
  @peutt hierarchyE Enum MF
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega
    bool bool eq (Tau (Ret true)) (Ret true).
Proof. apply peutt_of_pfinite. exact tau_ret_pfinite. Qed.

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
      bool).
  - apply pfinite_peutt_subrelation.
  - apply pfinite_tau_l.
  - apply peutt_refl.
Qed.
