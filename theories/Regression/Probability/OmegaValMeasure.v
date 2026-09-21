(** Role: DS1b standard-measure correspondence and isolation regressions.
    No FreeOmega, native backend, or PTree semantic interface is used. *)
Set Warnings "-notation-overridden,-ambiguous-paths,-redundant-canonical-projection".
Local Unset Universe Minimization ToSet.
From mathcomp Require Import all_ssreflect all_algebra reals boolp classical_sets
  ereal numfun measure probability.
From PTree.Prob.Domain Require Import Expectation MeasureModel.

Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Core.PTreeDefinition.ptree.

Set Implicit Arguments.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section StandardMeasure.
Variable R : realType.

Example bottom_is_standard_probability : probability (oval_carrier bool) R :=
  oval_probability (@oval_bottom R bool).

Example bottom_mass_one :
  oval_probability (@oval_bottom R bool) [set OVBottom] = 1%E.
Proof. by rewrite oval_probability_bottom /oval_mass /= subr0. Qed.

Example dirac_missing_mass_zero :
  oval_probability (oval_ret R true) [set OVBottom] = 0%E.
Proof. by rewrite oval_probability_bottom /oval_mass /= subrr. Qed.

Example distinct_returned_diracs :
  oval_probability (oval_ret R true) (oval_values [set true]) <>
  oval_probability (oval_ret R false) (oval_values [set true]).
Proof.
  rewrite !oval_probability_values /= !indicE.
  have HT : true \in [set true] by apply/asboolP.
  have HF : false \notin [set true] by apply/asboolPn; discriminate.
  rewrite HT (negbTE HF).
  move=> H; have H10 : (1 : R) = 0 := EFin_inj H.
  have /eqP := H10; by rewrite oner_eq0.
Qed.

Definition half_dirac_laws :
  OmegaValLaws (fun f : bool -> R => 2^-1 * f true).
Proof.
  have Hp : (0 : R) <= 2^-1 by rewrite invr_ge0 ler0n.
  have Hp1 : (2^-1 : R) <= 1 by rewrite invf_le1 // ler1n.
  constructor.
  - exact: mulr0.
  - intros f g Hf Hg Hfg; exact (ler_wpM2l Hp (Hfg true)).
  - intros p f H0 H1 Hf; by rewrite !mulrA [2^-1 * p]mulrC.
  - intros f g Hf Hg Hfg; exact: mulrDr.
  - by rewrite mulr1.
  - intros f Hf Hi; symmetry; exact (oval_sup_scale Hp (fun n => proj2 (Hf n true))).
Defined.
Definition half_dirac : OmegaVal R bool :=
  {| oval_eval := fun f => 2^-1 * f true; oval_laws := half_dirac_laws |}.

Example half_mass_at_bottom :
  oval_probability half_dirac [set OVBottom] = (1 - 2^-1)%:E.
Proof. by rewrite oval_probability_bottom /oval_mass /= mulr1. Qed.

Example half_mass_at_true :
  oval_probability half_dirac (oval_values [set true]) = (2^-1)%:E.
Proof.
  rewrite oval_probability_values /= indicE.
  have HT : true \in [set true] by apply/asboolP.
  by rewrite HT mulr1.
Qed.

Example bounded_expectation_recovered (L : OmegaVal R bool) :
  oval_eq (probability_oval (oval_probability L)) L.
Proof. exact: oval_probability_roundtrip. Qed.

Example arbitrary_standard_probability_recovered
    (p : probability (oval_carrier bool) R) U :
  oval_probability (probability_oval p) U = p U.
Proof. exact: probability_oval_roundtrip. Qed.

Example empty_carrier_probability_is_bottom (L : OmegaVal R Empty_set) :
  oval_probability L [set OVBottom] = 1%E.
Proof.
  rewrite oval_probability_bottom.
  have H : oval_mass L = 0.
  { rewrite /oval_mass -(oval_zero (oval_laws L)); apply oval_eval_ext=> x; case: x. }
  by rewrite H subr0.
Qed.
End StandardMeasure.
