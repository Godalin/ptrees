(** Checked native order theory. No recursive PTree frontier and no universe
    bypass: order compares returned-value events, not cemetery mass. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals
  boolp classical_sets functions fsbigop.
From mathcomp.analysis Require Import measure ereal.
From mathcomp Require Import numfun lebesgue_integral.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory HBNNSimple.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section OrderLaws.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).

Lemma mathcomp_native_sintegral_le {A} (mu nu : M A)
    (f : {nnsfun mc_carrier A >-> R}) :
  mathcomp_node_le mu nu -> f MCBottom = 0%R ->
  sintegral (mathcomp_kernel_root mu) f <=
  sintegral (mathcomp_kernel_root nu) f.
Proof.
  move=> Hle Hzero; rewrite !sintegralE lee_fsum // => r [t _ <-].
  case: (eqVneq (f t) 0%R) => [->|Hr]; first by rewrite !mul0e.
  apply: lee_pmul; try exact: measure_ge0; try by rewrite lee_fin.
  apply: Hle; first by [].
  move=> H; move: Hr; by rewrite -H Hzero eqxx.
Qed.

Lemma mathcomp_native_integral_le {A} (mu nu : M A)
    (f : mc_carrier A -> \bar R) :
  mathcomp_node_le mu nu ->
  (forall x, 0 <= f x) -> f MCBottom = 0 ->
  \int[mathcomp_kernel_root mu]_x f x <=
  \int[mathcomp_kernel_root nu]_x f x.
Proof.
  move=> Hle Hpos Hzero; rewrite !ge0_integralE //=.
  apply: ub_ereal_sup => _ [h /= Hh] <-.
  apply: ereal_sup_ge.
  exists (sintegral (mathcomp_kernel_root nu) h); first by exists h.
  apply: mathcomp_native_sintegral_le => //.
  apply/eqP; rewrite eq_le; apply/andP; split; last exact: fun_ge0.
  have := Hh MCBottom.
  by rewrite /patch mem_set // Hzero lee_fin.
Qed.

Lemma mathcomp_native_bind_le_mu {A B} (mu nu : M A) (k : A -> M B) :
  mathcomp_node_le mu nu ->
  mathcomp_node_le (mathcomp_kernel_bind mu k) (mathcomp_kernel_bind nu k).
Proof.
  move=> Hle U mU Hbot; rewrite !mathcomp_kernel_root_bind.
  apply: mathcomp_native_integral_le => //.
  change (dirac MCBottom U = (0 : \bar R)).
  rewrite /dirac indicE.
  have -> : (MCBottom \in U) = false by apply/asboolPn.
  reflexivity.
Qed.

Lemma mathcomp_native_le_antisym {A} (mu nu : M A) :
  mathcomp_node_le mu nu -> mathcomp_node_le nu mu -> mathcomp_kernel_eq mu nu.
Proof.
  move=> Hmn Hnm U mU Hb; apply/eqP.
  by rewrite eq_le (Hmn U mU Hb) (Hnm U mU Hb).
Qed.

(** These characterize any supplied lub as an order-theoretic supremum.
    They do not supply a lub witness, even for an increasing chain. *)
Lemma mathcomp_native_lub_upper {A} (chain : nat -> M A) out n :
  mathcomp_kernel_lub chain out -> mathcomp_node_le (chain n) out.
Proof.
  move=> H U mU Hb; rewrite (H U mU Hb).
  apply: ereal_sup_ge; exists (mathcomp_kernel_root (chain n) U); last exact: lexx.
  by exists n.
Qed.

Lemma mathcomp_native_lub_least {A} (chain : nat -> M A) out bound :
  mathcomp_kernel_lub chain out ->
  (forall n, mathcomp_node_le (chain n) bound) -> mathcomp_node_le out bound.
Proof.
  move=> Hlim Hbound U mU Hb; rewrite (Hlim U mU Hb).
  apply: ub_ereal_sup => _ [n _ <-]; exact (Hbound n U mU Hb).
Qed.

#[global] Instance MathCompNativeOrderLaws :
  @SemanticMeasureOrderLaws M (MathCompNodeSemanticMeasure R)
    (MathCompNodeSemanticOmega R).
Proof.
  constructor.
  - exact (@mathcomp_native_le_refl R).
  - exact (@mathcomp_native_le_trans R).
  - exact (@mathcomp_native_zero_le R).
  - exact @mathcomp_native_bind_le_mu.
  - exact (@mathcomp_native_bind_le_k R).
Qed.
End OrderLaws.
