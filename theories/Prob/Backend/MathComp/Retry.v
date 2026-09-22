(** A native semantic sanity check: a positive-probability retry equation
    has exactly the specified returned-value behavior. All checking enabled. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals boolp classical_sets.
From mathcomp Require Import measure ereal numfun.
From PTree.Prob.Backend.MathComp Require Import Kernel.
Set Implicit Arguments.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Retry.
Variable R : realType.
Lemma mathcomp_root_finite {A} (mu : MathCompKernelMeasure R A) U :
  mathcomp_kernel_root mu U \is a fin_num.
Proof.
  rewrite ge0_fin_numE; last exact: measure_ge0.
  apply: (le_lt_trans _ (ltry 1)).
  apply: (le_trans _ (mathcomp_kernel_root_le1 mu)).
  apply: le_measure => //.
  all: by rewrite inE.
Qed.

Lemma mathcomp_retry_fixed_point {A} (q : R) (mu target : MathCompKernelMeasure R A) :
  (0 < q <= 1)%R ->
  mathcomp_kernel_eq mu
    (mathcomp_kernel_bind (mathcomp_bernoulli q) (fun b => if b then target else mu)) ->
  mathcomp_kernel_eq mu target.
Proof.
  move=> /andP[Hq Hq1] He U mU Hb.
  have Hq01 : (0 <= q <= 1)%R by rewrite (ltW Hq) Hq1.
  have H := He U mU Hb.
  rewrite mathcomp_kernel_bind_bernoulli // in H.
  rewrite -(fineK (mathcomp_root_finite mu U))
    -(fineK (mathcomp_root_finite target U)) -!EFinM -EFinD in H.
  have Hr := EFin_inj H.
  rewrite -(fineK (mathcomp_root_finite mu U))
    -(fineK (mathcomp_root_finite target U)).
  congr (_%:E).
  apply: (mulfI (lt0r_neq0 Hq)).
  rewrite mulrBl mul1r addrCA in Hr.
  have Hzero : (q * fine (mathcomp_kernel_root target U) -
      q * fine (mathcomp_kernel_root mu U) = 0)%R.
  { apply: (addrI (fine (mathcomp_kernel_root mu U))).
    by rewrite addr0 -Hr. }
  move/eqP: Hzero; rewrite subr_eq0 => /eqP Hzero.
  exact: esym Hzero.
Qed.
End Retry.
