Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Program.Equality Classes.RelationClasses Relations.Relation_Operators.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure.
From PTree.Eq Require Import PEutt PTreeKernel
  PrimitiveStableHitting UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Complete stable hitting distinguishes silent divergence from return.
    This sanity check is independent of any finite-compression relation. *)
Variant closure_event : Type -> Type := .
Local Notation tree := (ptree closure_event SubEnum bool).
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation hit := (@ptree_hitting_approx closure_event SubEnum MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool).
Local Notation PE := (@peutt closure_event SubEnum MF FI
  FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega bool bool eq).

CoFixpoint closure_spin : tree := Tau closure_spin.
Definition closure_return : tree := Ret true.
Definition closure_delayed : tree := Tau closure_return.

Lemma closure_spin_approx_zero n : hit n (observe closure_spin) = FOZero.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (hit n (observe closure_spin) = FOZero). exact IH.
Qed.

Lemma closure_spin_not_peutt_return : ~ PE closure_spin closure_return.
Proof.
  intro Hpeutt.
  pose (out := FOLub (fun n => hit n (observe closure_spin))).
  assert (Hspin : @ptree_stable_hitting closure_event SubEnum MF FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
    (observe closure_spin) out).
  { apply free_omega_qlift_refl. intro h. reflexivity. }
  assert (Hret : @ptree_stable_hitting closure_event SubEnum MF FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
    (observe closure_return) (FORet (FHRet true))).
  { exact (@stable_hitting_ret closure_event SubEnum MF
      FI FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaObservableSemanticMeasureBindLaws
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega FreeOmegaObservableSemanticOmegaLaws
      FreeOmegaObservableSemanticOmegaCofinalityLaws bool true). }
  pose proof (peutt_hitting_lift Hpeutt Hspin Hret) as Hlift.
  pose proof (proj1 (free_omega_qlift_support Hlift)) as Hsupport.
  assert (Hempty : free_omega_ae (fun _ => False) out).
  { apply FOAELub. intro n. rewrite closure_spin_approx_zero. apply FOAEZero. }
  specialize (Hsupport _ Hempty). dependent destruction Hsupport.
  destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.
