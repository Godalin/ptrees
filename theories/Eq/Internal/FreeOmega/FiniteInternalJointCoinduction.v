(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq.Program Require Import Equality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed PTree.Prob.Interface.SemanticCoupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PStrong PrimitiveStableHitting UnifiedFrontier PTreeKernel PEutt.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalJoint FiniteInternalJointReference.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Pair-dependent finite cuts with structural residual lifting are a
    proved behavioral coinduction rule. Structural residual lifting is an
    explicit premise, not something recovered from arbitrary quotient equality. *)
Section PairedCoinduction.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI} {A B : Type}.
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Local Notation Pair := (ptree E MN A * ptree E MN B)%type.
Local Notation Heads := (stable_head E MN A * stable_head E MN B)%type.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable cut1 : Pair -> MF (ptree E MN A).
Variable cut2 : Pair -> MF (ptree E MN B).
Hypothesis cut1_valid : forall t u, sim t u ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A t (cut1 (t,u)).
Hypothesis cut2_valid : forall t u, sim t u ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure B u (cut2 (t,u)).
Hypothesis cuts_structural : forall t u, sim t u ->
  free_omega_lift (fun t u => pstrongF RR sim (observe t) (observe u)) (cut1 (t,u)) (cut2 (t,u)).
Hypothesis node_realizes : forall {X Y} (R : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift R mu nu ->
    exists joint, semantic_coupling R mu nu joint.

Theorem finite_internal_structural_pair_hitting t u out1 out2 :
  sim t u ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe t) out1 ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega B (observe u) out2 ->
  free_omega_qlift (stable_head_rel RR sim) out1 out2.
Proof.
  intros Hsim Hhit1 Hhit2.
  destruct (finite_internal_structural_paired_kernel_exists
    (@node_realizes) cuts_structural) as [kernel Hkernel].
  eapply finite_internal_reference_pair_hitting with
    (cut1 := cut1) (cut2 := cut2) (kernel := kernel)
    (left_reference := kernel) (right_reference := kernel) (t := t) (u := u).
  - exact cut1_valid.
  - exact cut2_valid.
  - exact (@node_realizes).
  - intros x y Hxy. exact (proj2 (proj2 (Hkernel x y Hxy))).
  - intros x y _. apply free_omega_qlift_refl. intro z. reflexivity.
  - intros x y _. apply free_omega_qlift_refl. intro z. reflexivity.
  - intros x y Hxy. exact (proj1 (Hkernel x y Hxy)).
  - intros x y Hxy. exact (proj1 (proj2 (Hkernel x y Hxy))).
  - exact Hsim.
  - exact Hhit1.
  - exact Hhit2.
Qed.

Theorem peutt_coinduction_finite_internal_structural t u :
  sim t u ->
  @peutt E MN MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A B RR t u.
Proof.
  intro Hsim. eapply peutt_coinduction with
    (sim := fun s1 s2 => exists x y,
      s1 = observe x /\ s2 = observe y /\ sim x y).
  - intros s1 s2 [x [y [-> [-> Hxy]]]].
    eapply stable_hitting_match_of_hitting_lift with
      (out1 := FOLub (fun n => @ptree_hitting_approx E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A n (observe x)))
      (out2 := FOLub (fun n => @ptree_hitting_approx E MN MF FI
        FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega B n (observe y))).
    + apply free_omega_qlift_refl. intro h. reflexivity.
    + apply free_omega_qlift_refl. intro h. reflexivity.
    + eapply FOQLMono with (T := stable_head_rel RR sim).
      * eapply finite_internal_structural_pair_hitting with (t := x) (u := y);
          [exact Hxy| |].
        -- apply free_omega_qlift_refl. intro h. reflexivity.
        -- apply free_omega_qlift_refl. intro h. reflexivity.
      * intros h1 h2 Hhead. dependent destruction Hhead.
        -- constructor. exact H.
        -- constructor. intro z. exists (k1 z), (k2 z).
           repeat split; try reflexivity. exact (H z).
  - exists t, u. repeat split; try reflexivity. exact Hsim.
Qed.

End PairedCoinduction.
