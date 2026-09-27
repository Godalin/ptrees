(** First-observation summaries: silent retries select an exit descriptor,
    whose interpretation may return or offer a visible event. Descriptors,
    not recursive stable heads, are sampled by MN. The complete frontier
    stays in FreeOmega MN. The complete-step profile at the end also supports
    arbitrary MF step frontiers via the generic adequacy theorem.
    No new iteration/cofinality capability is assumed. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure SupportLift Quotient.
From PTree.Eq Require Import PStruct PEutt UnifiedFrontier PTreeKernel.
From PTree.Eq.FreeOmega Require Import Base Bind Hitting Iter.
From PTree.Interp.FreeOmega Require Import IterationSummary.
From PTree.Interp Require Import FrontierIteration.
From PTree.Prob.FreeOmega Require Import BindOrder.
Set Implicit Arguments.
Unset Strict Implicit.

Section Absorption.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation W := (peutt (FI := FI) (FO := FO) eq).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).
Context {I B A : Type}.
Variable transition : I -> MN (I + B).
Variable exit_front : B -> MF (stable_head E MN A).

Definition absorbing_frontier i :=
  free_omega_bind (iteration_frontier (E := E) transition i)
    (stable_head_ret_bind_front exit_front).

(** Exact witness for the staged form. Exit frontiers may be mixed Ret/Vis,
    partial, and MF-valued; no normalization or continuation projection. *)
Theorem absorbing_iteration_summary
    (step : I -> ptree E MN (I + B)) (exit : B -> ptree E MN A)
    (Hstep : forall i, hits (step i)
      (FOSample (transition i) (fun next => FORet (FHRet next))))
    (Hexit : forall b, hits (exit b) (exit_front b)) i :
  hits (PTree.bind (PTree.iter step i) exit) (absorbing_frontier i).
Proof.
  apply stable_hitting_bind_ret_only.
  - eapply free_omega_ae_mono; [|apply iteration_frontier_returns].
    intros h [b ->]. constructor.
  - eapply iteration_frontier_summary_hitting; eassumption.
  - exact Hexit.
Qed.

(** Pushing exits into the loop preserves behavior, not literal visible
    continuation syntax. Compare every complete witness by whole-head
    lifting, keeping ALL responses of a visible continuation together. *)
Theorem absorbing_iteration_heads
    (step : I -> ptree E MN (I + B)) (exit : B -> ptree E MN A)
    (Hstep : forall i, hits (step i)
      (FOSample (transition i) (fun next => FORet (FHRet next))))
    (Hexit : forall b, hits (exit b) (exit_front b)) i out :
  hits (PTree.iter (pstruct_iter_natural_step step exit) i) out ->
  @sem_lift MF FI _ _ (stable_head_rel eq W) out (absorbing_frontier i).
Proof.
  intro Hout. eapply peutt_hitting_lift.
  - apply peutt_sym. exact (peutt_iter_natural step exit i).
  - exact Hout.
  - eapply absorbing_iteration_summary; eassumption.
Qed.

Theorem absorbing_iteration_exists
    (step : I -> ptree E MN (I + B)) (exit : B -> ptree E MN A)
    (Hstep : forall i, hits (step i)
      (FOSample (transition i) (fun next => FORet (FHRet next))))
    (Hexit : forall b, hits (exit b) (exit_front b)) i :
  exists out, hits (PTree.iter (pstruct_iter_natural_step step exit) i) out /\
    @sem_lift MF FI _ _ (stable_head_rel eq W) out (absorbing_frontier i).
Proof.
  destruct (ptree_stable_hitting_exists (FI := FI) (FO := FO)
    (observe (PTree.iter (pstruct_iter_natural_step step exit) i))) as [out Hout].
  exists out. split; [exact Hout|].
  eapply absorbing_iteration_heads; eassumption.
Qed.
End Absorption.

(** General profile: complete steps themselves may have arbitrary MF-valued
    mixed frontiers. All adequacy mathematics is in the generic theorem. *)
Section CompleteSteps.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Context {I A : Type} (step : I -> ptree E MN (I+A)).
Variable front : I -> MF (stable_head E MN (I+A)).

Definition complete_iteration_frontier i :=
  FOLub (fun n => iteration_summary_round (FI := FI) (FO := FO) step front n i).

Theorem complete_iteration_hitting
    (Hfront : forall i, ptree_stable_hitting (FI := FI) (FO := FO)
      (observe (step i)) (front i)) i :
  ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (PTree.iter step i)) (complete_iteration_frontier i).
Proof.
  eapply (iteration_summary_hitting (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure) (front := front)); try typeclasses eauto.
  - exact Hfront.
  - apply free_omega_qlift_refl. intros h. reflexivity.
Qed.
End CompleteSteps.
