(** DS5a foundations: countable representation and all-raw dual soundness.
    General joint realization is not claimed by these regressions. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype choice ssrnat ssralg ssrnum order reals.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Core.PTreeDefinition.ptree.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.FreeOmega Require Import Approximation Quotient.
From PTree.Prob.Backend.SubEnum Require Import Measure.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import
  Admissibility CountableSupport CouplingSoundness.
Fail Check PTree.Prob.Domain.MeasureModel.oval_probability.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Regression.Probability Require Import FreeOmegaDomain FreeOmegaQuotientDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Example empty_cover n : free_omega_enumerate (@FOZero SubEnum Empty_set) n = None.
Proof. reflexivity. Qed.

Example raw_invalid_cover :
  free_omega_ae (oval_enumerated (free_omega_enumerate alternating_bool)) alternating_bool.
Proof. exact: free_omega_enumerate_covers. Qed.

Definition returns_true (_ : unit) (b : bool) := b = true.
Lemma heterogeneous_invalid_middle : free_omega_qlift returns_true constant_unit (FORet true).
Proof.
  eapply FOQLComp with (mid := alternating_bool)
    (T := fun (_ : unit) (_ : bool) => True) (U := fun (_ : bool) b => b = true).
  - exact constant_to_invalid.
  - eapply FOQLComp with (mid := FORet tt)
      (T := fun (_ : bool) (_ : unit) => True) (U := fun (_ : unit) b => b = true).
    + exact invalid_to_ret.
    + apply FOQLStructural, FOLRet; reflexivity.
    + intros x b [y [_ Hb]]; exact Hb.
  - intros x b [y [_ Hb]]; exact Hb.
Qed.

Fixpoint geometric_prefix fuel start : FreeOmega SubEnum nat :=
  match fuel with
  | O => FOZero
  | S n => FOSample domain_fair
      (fun b => if b then FORet start else geometric_prefix n (S start))
  end.
Definition geometric := FOLub (fun n => geometric_prefix n O).

Lemma geometric_prefix_increasing fuel start :
  free_omega_approx eq (geometric_prefix fuel start) (geometric_prefix (S fuel) start).
Proof.
  induction fuel in start |- *; first apply FOApproxZero.
  cbn [geometric_prefix]; apply FOApproxSample with (S := eq).
  - apply sem_lift_refl; intro b; reflexivity.
  - intros b c ->; destruct c; [apply FOApproxRet; reflexivity|apply IHfuel].
Qed.

Lemma geometric_prefix_enumerates n start :
  exists i, free_omega_enumerate (geometric_prefix (S n) start) i = Some (Nat.add start n).
Proof.
  induction n in start |- *.
  - exists (pickle (O,O)); cbn [geometric_prefix free_omega_enumerate].
    rewrite pickleK; cbn; by rewrite Nat.add_0_r.
  - destruct (IHn (S start)) as [i Hi]; exists (pickle (1%nat,i)).
    cbn [geometric_prefix free_omega_enumerate]; rewrite pickleK.
    change (free_omega_enumerate (geometric_prefix (S n) (S start)) i = Some (Nat.add start (S n))).
    rewrite Hi; by rewrite Nat.add_succ_r Nat.add_succ_l.
Qed.

Example geometric_enumerates_all n : oval_enumerated (free_omega_enumerate geometric) n.
Proof.
  destruct (geometric_prefix_enumerates n O) as [i Hi].
  exists (pickle (S n,i)); cbn [geometric free_omega_enumerate]; rewrite pickleK; exact Hi.
Qed.

Section Tests.
Variable R : realType.

Lemma geometric_valid : free_omega_admissible R geometric.
Proof.
  apply admissible_lub_approx; last by intro n; apply geometric_prefix_increasing.
  intro n; generalize O as start; induction n=> start; first apply admissible_zero.
  cbn [geometric_prefix]; apply admissible_sample.
  intro b; destruct b; [apply admissible_ret|apply IHn].
Qed.

Example geometric_countable : oval_countably_supported (free_omega_domain geometric_valid).
Proof. exact: free_omega_domain_countable. Qed.

Example geometric_on_naturals :
  exists N : OmegaVal R nat,
    oval_mass N = oval_mass (free_omega_domain geometric_valid) /\
    oval_ae N (fun n => exists x, free_omega_enumerate geometric n = Some x) /\
    oval_eq (free_omega_domain geometric_valid)
      (oval_bind N (oval_decode R (free_omega_enumerate geometric))).
Proof. exact: free_omega_domain_countable_representation. Qed.

Example countable_cover_is_not_validity : ~ free_omega_admissible R alternating_bool.
Proof. exact: alternating_bool_not_admissible. Qed.

Example heterogeneous_dual_through_invalid :
  oval_bidual returns_true (free_omega_domain (constant_valid_by_quotient R))
    (free_omega_domain (@admissible_ret R bool true)).
Proof. apply free_omega_qlift_domain_bidual; exact heterogeneous_invalid_middle. Qed.

Example equality_joint_through_invalid :
  oval_joint eq (free_omega_domain (constant_valid_by_quotient R))
    (free_omega_domain (@admissible_ret R unit tt))
    (oval_bind (free_omega_domain (constant_valid_by_quotient R))
      (fun x => oval_ret R (x,x))).
Proof. apply free_omega_qlift_eq_joint; exact equality_through_invalid_middle. Qed.

Example zero_joint_empty_relation :
  oval_joint (fun (_ : bool) (_ : nat) => False)
    (oval_bottom R) (oval_bottom R) (oval_bottom R).
Proof. split; [by intros|split; by intros]. Qed.

Example nonzero_joint_empty_relation_impossible :
  ~ oval_coupled (fun (_ : bool) (_ : nat) => False) (oval_ret R true) (oval_ret R O).
Proof.
  intros [J HJ]; have H := proj1 (oval_joint_dual HJ).
  have Hbad := H (fun _ => 1) (fun _ => 0) (oval_test_one R) (oval_test_zero R)
    (fun x y Hfalse => False_rect _ Hfalse).
  change (is_true (1 <= (0 : R))) in Hbad; by rewrite ler10 in Hbad.
Qed.

Example unequal_mass_no_joint :
  ~ oval_coupled (fun (_ : unit) (_ : unit) => True) (oval_bottom R) (oval_ret R tt).
Proof.
  intros [J HJ]; have H := oval_bidual_mass (oval_joint_dual HJ).
  change (0 = (1 : R)) in H.
  have Hne : (1 : R) != 0 by apply oner_neq0.
  by rewrite -H eqxx in Hne.
Qed.
End Tests.
