(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt StableHittingComputation.
From PTree.Eq.FreeOmega Require Import Hitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Clients compute without unfolding stable hitting.  These regressions
    apply to every qualifying native backend, not just SubEnum. *)
Section ComputationRegressions.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation K R := (@ptree_primitive_kernel E MN MF FI FreeOmegaMixedMeasure R).
Local Notation hits t out :=
  (@stable_hitting MF FI FO _ _ (K _) (observe t) out).

Example two_tau_compute {R} (t : ptree E MN R) out :
  hits (Tau (Tau t)) out <-> hits t out.
Proof.
  rewrite !(stable_hitting_tau (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)). reflexivity.
Qed.

Example dirac_tau_compute {R X} (x : X) (k : X -> ptree E MN R) out :
  hits (Prob (sem_ret x) (fun y => Tau (k y))) out <-> hits (k x) out.
Proof.
  rewrite stable_hitting_prob_dirac_iff.
  apply (stable_hitting_tau (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)).
Qed.

(** Arbitrarily many branches may require different finite Tau depths.
    The result uses branch limits, not a maximum depth or finite support. *)
Example nonuniform_tau_depth_compute {R X}
    (mu : MN X) (depth : X -> nat) (k : X -> ptree E MN R)
    (front : X -> MF (stable_head E MN R)) :
  (forall x, hits (k x) (front x)) ->
  hits (Prob mu (fun x => Nat.iter (depth x) (fun u => Tau u) (k x)))
    (FOSample mu front).
Proof.
  intro Hfront.
  eapply (stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros x _. apply (proj2 (stable_hitting_tau_iter _ _ _)). apply Hfront.
Qed.

Example nested_joint_compute {X Y} (mu : MN X) (nu : X -> MN Y) :
  hits (Prob mu (fun x => Prob (nu x) (fun y => Ret (x,y))))
    (FOSample mu (fun x => FOSample (nu x) (fun y => FORet (FHRet (x,y))))).
Proof.
  eapply (stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros x _. eapply (stable_hitting_prob (FI := FI) (FO := FO)
      (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros y _. apply (stable_hitting_ret (FI := FI) (FO := FO)).
Qed.

Example nested_flatten_compute {R X Y}
    (mu : MN X) (nu : X -> MN Y) (k : Y -> ptree E MN R) out :
  hits (Prob mu (fun x => Prob (nu x) (fun y => Tau (k y)))) out <->
  hits (Prob (sem_bind mu nu) (fun y => Tau (k y))) out.
Proof. apply stable_hitting_prob_flatten_iff. Qed.

(** Sampling stops at Vis: its continuation is retained, not executed. *)
Example sampled_visible_head_compute {R X Y}
    (mu : MN X) (e : E Y) (k : X -> Y -> ptree E MN R) :
  hits (Prob mu (fun x => Tau (Vis e (k x))))
    (FOSample mu (fun x => FORet (FHVis e (k x)))).
Proof.
  eapply (stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros x _. apply (proj2 (stable_hitting_tau_iff _ _)).
    apply (stable_hitting_vis (FI := FI) (FO := FO)).
Qed.
End ComputationRegressions.
