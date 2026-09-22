(** Gate S: native order without gluing, a completion or recursive frontiers. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals
  boolp classical_sets.
From mathcomp.analysis Require Import measure ereal.
From mathcomp Require Import numfun.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws OrderLaws.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_frontier.
Set Implicit Arguments.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section NativeOrder.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).

Definition checked_native_order : @SemanticMeasureOrderLaws M NI NO := _.
Fail Definition still_missing_native_omega : @SemanticOmegaLaws M NI NO := _.

Example bottom_below_return :
  mathcomp_node_le (@mathcomp_kernel_zero R bool) (mathcomp_kernel_ret R true).
Proof. exact: mathcomp_native_zero_le. Qed.

(** The order does not compare cemetery events. At bottom the inequality
    actually goes the other way: this is why the integral lemma needs f(bottom)=0. *)
Example cemetery_mass_not_monotone :
  mathcomp_kernel_root (@mathcomp_kernel_zero R bool) [set MCBottom] = 1 /\
  mathcomp_kernel_root (mathcomp_kernel_ret R true) [set MCBottom] = 0.
Proof.
  split.
  - rewrite /mathcomp_kernel_zero /mathcomp_kernel_root /mathcomp_source_kernel
      /mathcomp_source_measure /mathcomp_bottom_measure /dirac.
    change ((indic [set (@MCBottom bool)] MCBottom : R)%:E = 1).
    rewrite indicE.
    have -> : (MCBottom \in [set (@MCBottom bool)]) = true by apply/asboolP.
    reflexivity.
  - rewrite mathcomp_kernel_root_ret /dirac indicE.
    have -> : (MCValue true \in [set MCBottom]) = false by apply/asboolPn; discriminate.
    reflexivity.
Qed.

Definition discard_false (b : bool) : M bool :=
  if b then mathcomp_kernel_ret R true else mathcomp_kernel_zero R.
Definition keep_both (_ : bool) : M bool := mathcomp_kernel_ret R true.

Example partial_sampling_returned_mass (q : R) (Hq : (0 <= q <= 1)%R) :
  mathcomp_kernel_root (mathcomp_kernel_bind (mathcomp_bernoulli q) discard_false)
    mc_returned = q%:E.
Proof.
  rewrite mathcomp_kernel_bind_bernoulli // /discard_false.
  rewrite (mathcomp_native_zero_returned R) // mule0 adde0.
  rewrite mathcomp_kernel_root_ret /dirac indicE.
  have -> : (MCValue true \in mc_returned) = true by apply/asboolP.
  by rewrite mule1.
Qed.

(** Nonzero partial sampling followed by an arbitrary further kernel.
    The second bind consumes source monotonicity, not just pointwise order. *)
Example partial_sampling_bind_monotone {A} (q : R) (k : bool -> M A) :
  mathcomp_node_le
    (mathcomp_kernel_bind (mathcomp_kernel_bind (mathcomp_bernoulli q) discard_false) k)
    (mathcomp_kernel_bind (mathcomp_kernel_bind (mathcomp_bernoulli q) keep_both) k).
Proof.
  apply: mathcomp_native_bind_le_mu.
  apply: mathcomp_native_bind_le_k => [] [] /=.
  - exact: mathcomp_native_le_refl.
  - exact: mathcomp_native_zero_le.
Qed.

Example generic_source_bind_order {A B} (mu nu : M A) (k : A -> M B) :
  @sem_le M NI NO A mu nu ->
  @sem_le M NI NO B (sem_bind mu k) (sem_bind nu k).
Proof. exact: sem_bind_le_mu. Qed.

Example supplied_lub_is_least {A} (c : nat -> M A) out bound :
  mathcomp_kernel_lub c out ->
  (forall n, mathcomp_node_le (c n) bound) -> mathcomp_node_le out bound.
Proof. exact: mathcomp_native_lub_least. Qed.
End NativeOrder.
