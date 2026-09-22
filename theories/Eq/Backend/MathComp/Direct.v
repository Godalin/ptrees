(** Universe-unchecked direct MathComp assembly, NOT a safe backend theorem.
    MN = MF = the existing native kernel. No formal completion is used.
    Native probability mathematics remains in Prob/Backend/MathComp with
    universe checking enabled. See docs/MATHCOMP_DIRECT.md and Gate M.
    This first increment assembles syntax/hitting/peutt only; it does not
    claim general hitting existence or an omega-complete native instance. *)
Local Unset Universe Checking.
From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel PEutt.

Section Direct.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).

Definition mathcomp_direct_mixed : MixedMeasure M M := MX.
Definition mathcomp_direct_tree {E A} := ptree E M A.
Definition mathcomp_direct_head {E A} := stable_head E M A.
Definition mathcomp_direct_frontier {E A} := M (@mathcomp_direct_head E A).
Definition mathcomp_direct_kernel {E A} := @ptree_primitive_kernel E M M NI MX A.
Definition mathcomp_direct_hitting {E A} := @ptree_stable_hitting E M M NI MX NO A.

(** Gluing is a mathematical premise, independent of the universe bypass. *)
Context `{G : MathCompCouplingGluing R}.
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Definition mathcomp_direct_peutt {E A} := @peutt E M M NI NC MX NO A A eq.
Lemma mathcomp_direct_peutt_refl {E A} (t : @mathcomp_direct_tree E A) :
  mathcomp_direct_peutt t t.
Proof. exact (@peutt_refl E M M NI NC MX NO A t). Qed.
End Direct.
