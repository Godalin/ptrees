(** Role: DS3 equality/validity boundary tests. In particular, a genuine
    FOQLComp may have an inadmissible intermediate on another carrier.
    Neither quotient equality alone nor arbitrary relational lifting is
    a certificate that every raw term denotes a subprobability. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Interface Require Import Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Quotient Measure.
From PTree.Prob.Backend.SubEnum Require Import Measure.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import
  Admissibility QuotientSoundness.

Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Eq.PEutt.peutt.

From PTree.Regression.Probability Require Import FreeOmegaDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Notation observable_measure := (@FreeOmegaObservableSemanticMeasure
  SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega).

Definition constant_unit : FreeOmega SubEnum unit := FOLub (fun _ => FORet tt).

Lemma constant_to_invalid :
  free_omega_qlift (fun (_ : unit) (_ : bool) => True) constant_unit alternating_bool.
Proof. apply FOQLLub=> n; apply FOQLStructural; constructor; exact I. Qed.

Lemma invalid_to_ret :
  free_omega_qlift (fun (_ : bool) (_ : unit) => True) alternating_bool (FORet tt).
Proof.
  eapply FOQLComp with (mid := constant_unit) (T := fun _ _ => True) (U := eq).
  - apply FOQLLub=> n; apply FOQLStructural; constructor; exact I.
  - apply FOQLSym, FOQLLubConstantR, FOQLStructural; constructor; reflexivity.
  - intros x [] _; exact I.
Qed.

(** Deliberately use the inadmissible alternating carrier as FOQLComp's
    actual middle term. Do not replace this evidence with reflexivity. *)
Lemma equality_through_invalid_middle :
  free_omega_qlift eq constant_unit (FORet tt).
Proof.
  eapply FOQLComp with (mid := alternating_bool)
    (T := fun _ _ => True) (U := fun _ _ => True).
  - exact constant_to_invalid.
  - exact invalid_to_ret.
  - intros [] [] _; reflexivity.
Qed.

Lemma retry_quotient :
  @sem_eq _ observable_measure _
    (FOLub retry_approx) (FOLub (fun _ => FOLub retry_approx)).
Proof. apply FOQLLubConstantR, free_omega_qlift_refl; intros x; reflexivity. Qed.

Section Tests.
Variable R : realType.

Example invalid_middle_really_invalid : ~ free_omega_admissible R alternating_bool.
Proof. exact: alternating_bool_not_admissible. Qed.

Lemma constant_valid_by_quotient : free_omega_admissible R constant_unit.
Proof.
  apply (proj2 (free_omega_qlift_eq_admissible R equality_through_invalid_middle)).
  exact: admissible_ret.
Qed.

Example invalid_middle_does_not_block_soundness :
  oval_eq (free_omega_domain constant_valid_by_quotient)
    (free_omega_domain (@admissible_ret R unit tt)).
Proof. apply free_omega_qlift_eq_sound; exact equality_through_invalid_middle. Qed.

Example equality_alone_is_not_validity :
  free_omega_qlift eq alternating_bool alternating_bool /\
  ~ free_omega_admissible R alternating_bool.
Proof.
  split; [apply free_omega_qlift_refl; intros x; reflexivity|].
  exact: alternating_bool_not_admissible.
Qed.

Example invalid_not_equal_to_valid (t : FreeOmega SubEnum bool) :
  free_omega_admissible R t -> ~ @sem_eq _ observable_measure _ alternating_bool t.
Proof.
  intros Hv H; apply (@alternating_bool_not_admissible R).
  exact (proj2 (free_omega_sem_eq_admissible R H) Hv).
Qed.

Lemma retry_valid_by_quotient :
  free_omega_admissible R (FOLub (fun _ => FOLub retry_approx)).
Proof.
  apply (proj1 (free_omega_sem_eq_admissible R retry_quotient)).
  exact: unbounded_retry_admissible.
Qed.

Example unbounded_retry_quotient_sound :
  oval_eq (free_omega_domain (unbounded_retry_admissible R))
    (free_omega_domain retry_valid_by_quotient).
Proof. apply free_omega_sem_eq_sound; exact retry_quotient. Qed.

Example soundness_ignores_validity_proofs
    (H1 H2 : free_omega_admissible R constant_unit)
    (H3 : free_omega_admissible R (FORet tt)) :
  oval_eq (free_omega_domain H1) (free_omega_domain H3) /\
  oval_eq (free_omega_domain H2) (free_omega_domain H3).
Proof. split; apply free_omega_sem_eq_sound; exact equality_through_invalid_middle. Qed.

Example quotient_cannot_erase_missing_mass :
  ~ @sem_eq _ observable_measure _ (@FOZero SubEnum unit) (FORet tt).
Proof.
  intro H.
  have Heq := free_omega_sem_eq_sound (@admissible_zero R unit) (@admissible_ret R unit tt) H.
  have H01 := Heq (fun _ => 1) (oval_test_one R).
  change (0 = (1 : R)) in H01.
  have Hneq : (1 : R) != 0 by apply oner_neq0.
  by rewrite -H01 eqxx in Hneq.
Qed.
End Tests.
