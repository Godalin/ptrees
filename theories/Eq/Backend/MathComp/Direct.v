(** Universe-unchecked direct MathComp assembly, NOT a safe backend theorem.
    MN = MF = the existing native kernel. No formal completion is used.
    Native probability mathematics remains in Prob/Backend/MathComp with
    universe checking enabled. See docs/MATHCOMP_DIRECT.md and Gate M.
    Native order, omega, diagonal/Fubini and relational bind are checked in
    Gate S. Only their recursive-frontier instantiation belongs to Gate M. *)
Local Unset Universe Checking.
From mathcomp Require Import reals boolp.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws
  OrderLaws OmegaLaws BindLaws BindOrder.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import Shallow UnifiedFrontier PTreeKernel PEutt
  PrimitiveStableHitting StableHittingRelation Bind BindScheduling.
From PTree.Eq Require Import Canonical.

(** Only this existing unchecked assembly registers the direct route. No
    safe facade imports it; probability mathematics remains in Gate S. *)
#[global] Instance MathComp_CanonicalBehavior (R : realType) :
    CanonicalBehavior (MathCompKernelMeasure R) := {|
  behavior_frontier := MathCompKernelMeasure R;
  behavior_measure := MathCompNodeSemanticMeasure R;
  behavior_mixed := MathCompNativeMixedMeasure R;
  behavior_omega := MathCompNodeSemanticOmega R
|}.

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

Lemma mathcomp_direct_hitting_exists {E A} (t : @mathcomp_direct_tree E A) :
  exists out, mathcomp_direct_hitting (observe t) out.
Proof. apply ptree_stable_hitting_exists. Qed.

(** Gluing is a mathematical premise, independent of the universe bypass. *)
Context `{G : MathCompCouplingGluing R}.
Local Notation NC := (@MathCompNodeSemanticMeasureCoreLaws R G).
Definition mathcomp_direct_peutt {E A} := @peutt E M M NI NC MX NO A A eq.
Lemma mathcomp_direct_peutt_refl {E A} (t : @mathcomp_direct_tree E A) :
  mathcomp_direct_peutt t t.
Proof. exact (@peutt_refl E M M NI NC MX NO A t). Qed.

Section Bind.
Context {E : Type -> Type}.
(** All probability obligations are checked native instances. Only this
    recursive-frontier instantiation needs the existing Gate M relaxation. *)
Theorem mathcomp_direct_bind_cofinal {A B}
    (t : ptree E M A) (k : A -> ptree E M B) :
  @ptree_bind_cofinal E M M NI MX NO A B t k.
Proof.
  apply BindScheduling.ptree_bind_cofinal_all.
  - exact (@sem_bind_ret_order M NI NO (MathCompNativeBindOrderLaws R)).
  - exact (@sem_bind_zero_order M NI NO (MathCompNativeBindOrderLaws R)).
  - exact (@mixed_bind_assoc_order M M NI MX NO (MathCompNativeMixedBindOrderLaws R)).
  - exact (@mixed_bind_le_k M M NI MX NO (MathCompNativeMixedBindOrderLaws R)).
  - exact (@sem_lub_cofinal M NI NO (MathCompNativeDirectedCofinalityLaws R)).
Qed.

(** Fully heterogeneous eventful bind: exactly the generic theorem, not a
    second native coinduction or a separate witness-choice proof. *)
Theorem mathcomp_direct_peutt_bind {A B C D}
    (RR : A -> B -> Prop) (RS : C -> D -> Prop)
    (t : ptree E M A) (u : ptree E M B)
    (k : A -> ptree E M C) (h : B -> ptree E M D) :
  @peutt E M M NI NC MX NO A B RR t u ->
  (forall x y, RR x y -> @peutt E M M NI NC MX NO C D RS (k x) (h y)) ->
  @peutt E M M NI NC MX NO C D RS (PTree.bind t k) (PTree.bind u h).
Proof. apply peutt_bind. Qed.
End Bind.
End Direct.
