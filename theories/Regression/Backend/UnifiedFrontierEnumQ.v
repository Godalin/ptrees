(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

From mathcomp Require Import ssreflect ssrbool eqtype.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Regression.Backend Require Import EnumQMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.

(** Native EnumQ samples live below heads containing recursive trees.  Use
    FreeOmega for those heads: sharing the monomorphic EnumQ interface at
    both levels imposes universe constraints incompatible with other clients. *)
Local Notation MF := (FreeOmega EnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)).
Definition unified_reg_split_heads :
    MF (stable_head regE EnumQ bool) :=
  FOSample reg_fair_split (fun b => FORet (FHRet b)).

Lemma reg_split_program_unified_frontier :
  @frontier_certificate regE EnumQ MF EnumQ_SemanticMeasure FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
    (observe reg_split_program) unified_reg_split_heads.
Proof.
  unfold reg_split_program, unified_reg_split_heads.
  apply (@UFProb regE EnumQ MF EnumQ_SemanticMeasure FI
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool bool
    reg_fair_split (fun b => Ret b) (fun b => FORet (FHRet b))
    (fun _ => True)).
  - apply sem_ae_true.
  - move=> b _. constructor.
Qed.

(** Literal duplication and mass splitting remain invisible at the unified
    semantic layer because its EnumQ equality is the extensional coupling
    equality, not list equality. *)
Lemma unified_reg_split_extensional :
  @sem_eq MF FI _ unified_reg_split_heads
    (FOSample reg_fair (fun b => FORet (FHRet b))).
Proof.
  eapply FOQLSample with (T := fun x y : bool => y = x).
  - apply sem_lift_sym. exact reg_split_mass_lift_eq.
  - intros x y ->. apply free_omega_qlift_refl. intro h. reflexivity.
Qed.
