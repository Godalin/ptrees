(** Gate M only. Never imported by the safe AllImports aggregate.
    These are capability probes, not completed direct-backend acceptance.
    The checked negative counterparts remain in MathCompUniverse.v. *)
Local Unset Universe Checking.
Require PTree.Regression.Backend.FreeOmegaUpperContracts.
From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws OrderLaws.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt.
From PTree.Eq.Backend.MathComp Require Import Direct.

Section Probes.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Local Notation E := (fun _ : Type => Empty_set).

Definition direct_ret : ptree E M bool := Ret true.
Definition direct_frontier : Type := @mathcomp_direct_frontier R E bool.
Definition direct_kernel := @mathcomp_direct_kernel R E bool.
Definition direct_hitting := @mathcomp_direct_hitting R E bool.

(** Order is now proved in Gate S. Omega remains missing mathematics, not
    a universe error. No supplied
    assumptions stand in for these instances. Replace each negative probe
    with a positive one when its checked native proof is implemented. *)
Definition available_native_order : @SemanticMeasureOrderLaws M NI NO := _.
Fail Definition missing_native_omega : @SemanticOmegaLaws M NI NO := _.
Fail Definition missing_general_hitting_exists :=
  @ptree_stable_hitting_exists E M M NI NI MX NO _ _ bool.

Context `{G : MathCompCouplingGluing R}.
Example direct_ret_reflexivity :
  @mathcomp_direct_peutt R G E bool direct_ret direct_ret.
Proof. apply mathcomp_direct_peutt_refl. Qed.

Example direct_eventful_reflexivity {F A} (t : ptree F M A) :
  @mathcomp_direct_peutt R G F A t t.
Proof. apply mathcomp_direct_peutt_refl. Qed.
End Probes.
