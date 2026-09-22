(** Phase 2 contracts: common finite algebra, without migrating a backend.
    Rational and real scalars use the same records; carriers need no equality,
    inhabitation, countability or MathComp packed structure. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.

Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Prob.Legacy.RatSubTypes.nnQ.
Fail Check PTree.Prob.Backend.SubEnumQ.Measure.SubEnumQ.
Fail Check PTree.Prob.Backend.SubEnumR.Representation.SubEnumR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section OrderedScalar.
Variable R : numDomainType.

(** Duplicate values are not normalized away, and raw weighting mass may
    exceed one. Only the outer FiniteSubdist refinement excludes this. *)
Definition duplicate_weighting : FiniteEnum R bool.
Proof.
  refine (finite_enum_of_list (mu := [(1,true); (1,true); (0,false)]) _).
  intros p b [H|[H|[H|[]]]]; inversion H; subst; try exact: ler01; exact: lexx.
Defined.
Example duplicate_raw_preserved :
  finite_enum_raw duplicate_weighting = [(1,true); (1,true); (0,false)].
Proof. reflexivity. Qed.
Example weighting_mass_two : finite_mass duplicate_weighting = 1 + 1.
Proof. by rewrite /finite_mass /finite_enum_expect /= !mulr1 !addr0. Qed.
Example overweight_not_subdistribution : ~ finite_mass duplicate_weighting <= 1.
Proof.
  rewrite weighting_mass_two; intro H.
  have Hlt : (1 : R) < 1 + 1 by rewrite ltrDl ltr01.
  have Hbad := lt_le_trans Hlt H; by rewrite ltxx in Hbad.
Qed.

Example negative_list_rejected : ~ @finite_nonnegative R bool [(-1,true)].
Proof.
  intro H; have Hn := H (-1) true (or_introl (Logic.eq_refl _)).
  by rewrite oppr_ge0 ler10 in Hn.
Qed.
Fail Definition missing_sign_proof : FiniteEnum R bool :=
  finite_enum_of_list [(1,true)].
Fail Definition missing_mass_proof : FiniteSubdist R bool :=
  @Build_FiniteSubdist R bool duplicate_weighting.

Definition null_branch : FiniteSubdist R bool.
Proof.
  refine (finite_subdist_of_list (mu := [(1,true); (0,false)]) _ _).
  - intros p b [H|[H|[]]]; inversion H; subst; [exact: ler01|exact: lexx].
  - by rewrite /= !mulr1 !addr0.
Defined.
Example null_branch_ignored :
  finite_subdist_expect null_branch (fun b => if b then 1 else -1) = 1.
Proof. by rewrite /finite_subdist_expect /finite_enum_expect /= mul1r mul0r !addr0. Qed.
Example null_branch_ae_ext :
  finite_subdist_expect null_branch (fun b => if b then 1 else -1) =
  finite_subdist_expect null_branch (fun _ => 1).
Proof.
  apply finite_expect_ae_ext.
  - exact (finite_enum_nonnegative (finite_subdist_enum null_branch)).
  - intros p b [H|[H|[]]] Hnz; inversion H; subst; first reflexivity.
    exfalso; exact (Hnz (Logic.eq_refl _)).
Qed.
Example bind_preserves_probability {A B} (mu : FiniteSubdist R A)
    (k : A -> FiniteSubdist R B) :
  finite_mass (finite_subdist_enum (finite_subdist_bind mu k)) <= 1.
Proof. exact (finite_subdist_mass_bound _). Qed.
Example bind_preserves_nonnegative {A B} (mu : FiniteSubdist R A)
    (k : A -> FiniteSubdist R B) :
  finite_nonnegative (finite_enum_raw (finite_subdist_enum (finite_subdist_bind mu k))).
Proof. exact (finite_enum_nonnegative _). Qed.
Example bind_computes_by_expectation {A B} (mu : FiniteSubdist R A)
    (k : A -> FiniteSubdist R B) f :
  finite_subdist_expect (finite_subdist_bind mu k) f =
  finite_subdist_expect mu (fun x => finite_subdist_expect (k x) f).
Proof. exact: finite_subdist_expect_bind. Qed.
Example empty_result_carrier : finite_mass (finite_subdist_enum (@finite_subdist_zero R Empty_set)) = 0.
Proof. reflexivity. Qed.
End OrderedScalar.

Section RationalScalar.
Lemma half_nonnegative : (0 : rat) <= 1 / 2.
Proof. apply divr_ge0; [exact: ler01|exact: ler0n]. Qed.
Lemma half_bounded : (1 : rat) / 2 <= 1.
Proof. by rewrite ler_pdivrMr ?ltr0n // mul1r ler1n. Qed.
Definition rational_half :=
  finite_subdist_scale half_nonnegative half_bounded (finite_subdist_ret _ true).
Example rational_half_mass : finite_mass (finite_subdist_enum rational_half) = (1 : rat) / 2.
Proof. by rewrite /rational_half /= finite_mass_scale finite_mass_ret mulr1. Qed.
Example rational_bind_quarter :
  finite_subdist_expect (finite_subdist_bind rational_half (fun _ => rational_half)) (fun _ => 1) =
  ((1 : rat) / 2) * (1 / 2).
Proof.
  rewrite finite_subdist_expect_bind /rational_half !finite_subdist_expect_scale.
  by rewrite !finite_subdist_expect_ret mulr1.
Qed.
End RationalScalar.

Section RealScalar.
Variable R : realType.
Lemma sqrt_weight_nonnegative : (0 : R) <= Num.sqrt (1 / 2).
Proof. exact: sqrtr_ge0. Qed.
Lemma sqrt_weight_bounded : Num.sqrt ((1 : R) / 2) <= 1.
Proof.
  have Hhalf : (1 : R) / 2 <= 1 by rewrite ler_pdivrMr ?ltr0n // mul1r ler1n.
  have H := ler_wsqrtr Hhalf; by rewrite sqrtr1 in H.
Qed.
Definition real_partial : FiniteSubdist R bool :=
  finite_subdist_scale sqrt_weight_nonnegative sqrt_weight_bounded (finite_subdist_ret R true).
Example real_weight_without_rational_encoding :
  finite_subdist_expect real_partial (fun _ => 1) = Num.sqrt ((1 : R) / 2).
Proof. by rewrite /real_partial finite_subdist_expect_scale finite_subdist_expect_ret mulr1. Qed.
End RealScalar.

Section HighCarrier.
Universe u.
Variable R : numDomainType.
Definition high_finite_dirac (A : Type@{u}) : FiniteSubdist R Type@{u} := finite_subdist_ret R A.
Example high_finite_bind (A : Type@{u}) (f : Type@{u} -> R) :
  finite_subdist_expect
    (finite_subdist_bind (high_finite_dirac A) (fun X => finite_subdist_ret R X)) f = f A.
Proof. by rewrite finite_subdist_bind_ret_r /high_finite_dirac finite_subdist_expect_ret. Qed.
End HighCarrier.
