(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import ClassicalChoice ChoiceFacts.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed PTree.Prob.Interface.SemanticCoupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Native PTree.Prob.FreeOmega.JointExtension.
From PTree.Eq Require Import PStrong.
From PTree.Eq.Internal Require Import FiniteInternalPlan.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalNative FiniteInternalRoundCoupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Assemble a full native round from an explicit compression-path joint.
    Only its graph marginals are quotient certificates.  Matched guards
    expose native liftings, which the supplied NODE realizer turns into
    conditional joints.  No quotient-to-native reflection is assumed. *)
Section NativeJoint.
Universes node node_rep frontier.
Context {E : Type -> Type} {MN : Type@{node} -> Type@{node_rep}}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {A B : Type}.
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Let Anchor : Type@{frontier} := (ptree E MN A * ptree E MN B)%type.
Local Notation qlift := (@free_omega_qlift@{
  frontier frontier node node node node node node node node node node frontier frontier frontier
  node node node node node_rep node node node node node node node node
  node node node node node node node node node node} MN NI NO _ _).

Hypothesis node_realizes : forall {X Y : Type@{node}} (R : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift R mu nu ->
    exists joint, semantic_coupling R mu nu joint.

Context {t : ptree E MN A} {u : ptree E MN B}.
Variable p : finite_internal_plan t.
Variable q : finite_internal_plan u.
Context {Z : Type@{node}}.
Variable joint : MN Z.
Variable left : Z -> internal_plan_path p.
Variable right : Z -> internal_plan_path q.
Hypothesis joint_left : qlift (fun z x => left z = x)
  (FOSample joint (fun z => FORet z))
  (FOSample (internal_plan_measure p) (fun x => FORet x)).
Hypothesis joint_right : qlift (fun z y => right z = y)
  (FOSample joint (fun z => FORet z))
  (FOSample (internal_plan_measure q) (fun y => FORet y)).
Hypothesis joint_guard : sem_ae joint (fun z => (fun t u => pstrongF RR sim (observe t) (observe u))
  (internal_plan_residual p (left z)) (internal_plan_residual q (right z))).

Theorem finite_internal_native_joint_round :
  exists (W : Type@{node}) (round : MN W)
    (project_left : W -> native_sample_type (internal_plan_round_native p))
    (project_right : W -> native_sample_type (internal_plan_round_native q)),
    qlift (fun w x => project_left w = x)
      (FOSample round (fun w => FORet w))
      (FOSample (native_sample_measure (internal_plan_round_native p)) (fun x => FORet x)) /\
    qlift (fun w y => project_right w = y)
      (FOSample round (fun w => FORet w))
      (FOSample (native_sample_measure (internal_plan_round_native q)) (fun y => FORet y)) /\
    sem_ae round (fun w => internal_round_path_rel RR sim p q
      (project_left w) (project_right w)).
Proof.
  pose (Good := fun z => (fun t u => pstrongF RR sim (observe t) (observe u))
    (internal_plan_residual p (left z)) (internal_plan_residual q (right z))).
  pose (U := fun x => native_sample_type (internal_guard_native (internal_plan_residual p x))).
  pose (V := fun y => native_sample_type (internal_guard_native (internal_plan_residual q y))).
  pose (lk := fun x => native_sample_measure (internal_guard_native (internal_plan_residual p x))).
  pose (rk := fun y => native_sample_measure (internal_guard_native (internal_plan_residual q y))).
  pose (Rguard := fun z (gx : U (left z)) (gy : V (right z)) =>
    internal_round_target_rel RR sim
      (native_sample_value (internal_guard_native (internal_plan_residual p (left z))) gx)
      (native_sample_value (internal_guard_native (internal_plan_residual q (right z))) gy)).
  assert (Hex : forall z, exists conditional : MN (U (left z) * V (right z)),
    Good z -> semantic_coupling (Rguard z) (lk (left z)) (rk (right z)) conditional).
  { intro z. destruct (classic (Good z)) as [Hz|Hz].
    - destruct (node_realizes (internal_guard_native_coupled Hz)) as [row Hrow].
      exists row. intros _. exact Hrow.
    - exists sem_zero. intro Hgood. contradiction. }
  destruct (@non_dep_dep_functional_choice (@choice) Z
    (fun z => MN (U (left z) * V (right z)))
    (fun z row => Good z -> semantic_coupling (Rguard z)
      (lk (left z)) (rk (right z)) row) Hex) as [conditional Hconditional].
  exists (extended_joint_path left right U V),
    (extended_joint_measure joint conditional),
    (@extended_joint_left _ _ _ left right U V),
    (@extended_joint_right _ _ _ left right U V).
  split.
  - exact (extended_joint_left_marginal (Anchor := Anchor)
      joint_left joint_guard Hconditional).
  - split.
    + exact (extended_joint_right_marginal (Anchor := Anchor)
        joint_right joint_guard Hconditional).
    + eapply sem_ae_mono; [|exact (extended_joint_support joint_guard Hconditional)].
      intros [z [gx gy]] [_ Hrel]. exact Hrel.
Qed.
End NativeJoint.
