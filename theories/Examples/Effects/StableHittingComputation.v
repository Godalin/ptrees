(** Role: supporting program/semantic example, not a flagship claim. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import UnifiedFrontier PrimitiveStableHitting PTreeKernel PEutt StableHittingComputation.
From PTree.Eq.FreeOmega Require Import Hitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Clients compute without unfolding stable hitting.  These regressions
    apply to every qualifying native backend, not just SubEnumQ. *)
Section ComputationRegressions.
Context {E MN : Type → Type}
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

Example dirac_tau_compute {R X} (x : X) (k : X → ptree E MN R) out :
  hits (Prob (sem_ret x) (λ y, Tau (k y))) out ↔ hits (k x) out.
Proof.
  rewrite stable_hitting_prob_dirac_iff.
  apply (stable_hitting_tau (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)).
Qed.

(** Arbitrarily many branches may require different finite Tau depths.
    The result uses branch limits, not a maximum depth or finite support. *)
Example nonuniform_tau_depth_compute {R X}
    (mu : MN X) (depth : X → nat) (k : X → ptree E MN R)
    (front : X → MF (stable_head E MN R)) :
  (∀ x, hits (k x) (front x)) →
  hits (Prob mu (λ x, Nat.iter (depth x) (λ u, Tau u) (k x)))
    (FOSample mu front).
Proof.
  intro Hfront.
  eapply (stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := λ _, True).
  - apply sem_ae_true.
  - intros x _. apply (proj2 (stable_hitting_tau_iter _ _ _)). apply Hfront.
Qed.

(** Sampling stops at Vis: its continuation is retained, not executed. *)
Example sampled_visible_head_compute {R X Y}
    (mu : MN X) (e : E Y) (k : X → Y → ptree E MN R) :
  hits (Prob mu (λ x, Tau (Vis e (k x))))
    (FOSample mu (λ x, FORet (FHVis e (k x)))).
Proof.
  eapply (stable_hitting_prob (FI := FI) (FO := FO)
    (MX := FreeOmegaMixedMeasure)) with (Good := λ _, True).
  - apply sem_ae_true.
  - intros x _. apply (proj2 (stable_hitting_tau_iff _ _)).
    apply (stable_hitting_vis (FI := FI) (FO := FO)).
Qed.
End ComputationRegressions.
