(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Automatic Proposition Inductives.

Require Import RelationClasses.
From Coq.Program Require Import Equality.

From PTree.Core Require Import PTreeDefinition.
From PTree.API Require Import EnumQ.
Require Import PTree.Prob.Backend.EnumQ.Representation.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import PStruct PStrong PEutt ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Import Base Guarded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Variant hierarchyE : Type -> Type := .
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation W :=
  (@peutt hierarchyE SubEnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool bool eq).

Lemma behavioral_equivalence_regression : Equivalence W.
Proof. exact peutt_equivalence. Qed.

(** Tau transparency does not assert termination of the residual program. *)
CoFixpoint hierarchy_spin : ptree hierarchyE SubEnumQ bool := Tau hierarchy_spin.

Lemma tau_before_divergence : W (Tau hierarchy_spin) hierarchy_spin.
Proof. apply peutt_tau_l. Qed.

Lemma tau_ret_not_pstrong :
  ~ @pstrong hierarchyE SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticMeasureCoreLaws bool bool eq
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


Lemma tau_ret_peutt : W (Tau (Ret true)) (Ret true).
Proof. apply peutt_tau_l. Qed.

(** The registered structural inclusion works under behavioral contexts. *)
Lemma structural_prob_context_rewrite {X} (mu : SubEnumQ X)
    (k1 k2 : X -> ptree hierarchyE SubEnumQ bool)
    (Hk : forall x, pstruct eq (k1 x) (k2 x)) :
  W (Prob mu k1) (Prob mu k2).
Proof.
  eapply peutt_prob_rewrite with (S := pstruct eq) (XR := eq).
  - intros t u Htu. apply peutt_of_pstruct, Htu.
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x y ->. apply Hk.
Qed.

Lemma strong_prob_coupled_context_rewrite {X Y}
    (XR : X -> Y -> Prop) (mu : SubEnumQ X) (nu : SubEnumQ Y)
    (k1 : X -> ptree hierarchyE SubEnumQ bool)
    (k2 : Y -> ptree hierarchyE SubEnumQ bool)
    (Hmu : sem_lift XR mu nu)
    (Hk : forall x y, XR x y -> pstrong eq (k1 x) (k2 y)) :
  W (Prob mu k1) (Prob nu k2).
Proof.
  eapply peutt_prob_rewrite with (S := pstrong eq).
  - intros t u Htu. apply peutt_of_pstrong, Htu.
  - exact Hmu.
  - exact Hk.
Qed.

(** A local administrative rewrite is justified by hitting transparency,
    even under a probability node with a divergent continuation. *)
Lemma tau_prob_divergent_branch (mu : SubEnumQ bool) :
  W (Prob mu (fun b : bool => Tau (if b then Ret true else hierarchy_spin)))
    (Prob mu (fun b : bool => if b then Ret true else hierarchy_spin)).
Proof.
  eapply peutt_prob with (XR := eq).
  - apply sem_lift_refl. intro b. reflexivity.
  - intros b b' ->. apply peutt_tau_l.
Qed.

Lemma tau_bind_context_rewrite
    (t : ptree hierarchyE SubEnumQ bool)
    (k : bool -> ptree hierarchyE SubEnumQ bool) :
  W (PTree.bind (Tau t) (fun x => Tau (k x))) (PTree.bind t k).
Proof.
  apply peutt_bind_Proper.
  - apply peutt_tau_l.
  - intro x. apply peutt_tau_l.
Qed.

Lemma tau_fmap_context_rewrite (f : bool -> bool)
    (t : ptree hierarchyE SubEnumQ bool) :
  W (PTree.fmap f (Tau t)) (PTree.fmap f t).
Proof. apply peutt_fmap_Proper, peutt_tau_l. Qed.
