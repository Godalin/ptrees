(** Native kernel algebra and the checked recursive-frontier boundary.
    Gate S keeps these negative probes; the separate Gate M direct client
    bypasses this check without repairing the universe inconsistency.
    No unsafe universe setting is used here, and no capability is assumed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
(** One existing maintained client suffices to expose the incompatible
    global universe constraints; a standalone file misses this boundary. *)
Require PTree.Regression.Backend.FreeOmegaUpperContracts.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt.

Section SafeCapabilities.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Definition self_mixed : MixedMeasure M M := MathCompNativeMixedMeasure R.
Definition self_unit : @MixedMeasureUnitLaws M M NI NI self_mixed := _.
Definition self_node_bind : @MixedMeasureNodeBindLaws M M NI NI self_mixed := _.
Definition self_total : @SemanticTotalProperLaws M NI NO := _.
Definition self_cofinality : @SemanticOmegaCofinalityLaws M NI NO := _.

Example self_nested_sampling {A B C} (mu : M A) (k : A -> M B) (h : B -> M C) :
  sem_lift eq (mixed_bind mu (fun x => mixed_bind (k x) h))
    (mixed_bind (sem_bind mu k) h).
Proof. exact (@mixed_bind_node_assoc M M NI NI self_mixed self_node_bind A B C mu k h). Qed.

Definition native_mathcomp_tree : Type := ptree (fun _ => Empty_set) M bool.
Definition native_mathcomp_head : Type := stable_head (fun _ => Empty_set) M bool.
(** The positive tree/head controls above succeed. The following commands
    fail specifically with a universe inconsistency, not a missing name.
    In isolation they can compile, but then their .vo cannot be jointly
    loaded with FreeOmegaUpperContracts / AllImports. *)
Fail Definition same_mathcomp_frontier : Type := M native_mathcomp_head.
Fail Definition same_mathcomp_primitive_kernel :=
  @ptree_primitive_kernel (fun _ => Empty_set) M M NI self_mixed bool.

Section ExistingGluingAssumption.
Context `{G : MathCompCouplingGluing R}.
Fail Definition same_mathcomp_peutt :=
  @peutt (fun _ => Empty_set) M M NI
    (@MathCompNodeSemanticMeasureCoreLaws R G) self_mixed NO bool bool eq.
End ExistingGluingAssumption.
End SafeCapabilities.
