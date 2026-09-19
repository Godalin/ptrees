Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob Require Import TwoLevelMeasureSubEnum FreeOmegaMeasure
  FreeOmegaUpperExpectationSubEnum FreeOmegaUpperObservationSubEnum.
From PTree.Examples Require Import RandomWalk FreeOmegaEscapingMass
  FreeOmegaUpperExpectation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section ObservationModelRegression.
Variable R : realType.
Local Notation upper := (free_omega_upper (R := R)).

Lemma unit_test_bounded : forall _ : unit, 0 <= (1 : R) /\ (1 : R) <= 1.
Proof. intro x. split; [exact: ler01|exact: lexx]. Qed.

(** The actual unbounded, infinite-state RandomWalk example, with its
    high-universe stable-head carrier, has numeric mass one.  This uses
    the direct hitting observation, not unproved quotient invariance. *)
Theorem random_walk_limit_upper_mass x y : upper (walk_limit x y) (fun _ => 1) = 1.
Proof.
  rewrite (free_omega_observes_upper (walk_limit_observes_unit x y)
    (f := fun _ : unit => (1 : R)) unit_test_bounded).
  change (ratr (1 : rat) * (1 : R) + 0 = 1).
  by rewrite rmorph1 mul1r addr0.
Qed.

Theorem increasing_kernel_observation_upper_mass x :
  upper (FOLub (EscapingMass.kernel x)) (fun _ => 1) = 1.
Proof.
  rewrite (free_omega_observes_upper (EscapingMass.increasing_kernel_observable x)
    (f := fun _ : unit => (1 : R)) unit_test_bounded).
  by rewrite enum_real_expect_one EscapingMass.big_mass_one rmorph1.
Qed.

(** A second, NUMERIC rejection of the former escaping-mass observation.
    It deliberately does not use inversion of FOOObserveLub or the earlier
    escaped_row_not_observable theorem. *)
Theorem escaped_row_wrong_mass_rejected_numerically n :
  ~ @free_omega_observes SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    unit unit (fun x => x) (FOLub (fun x => EscapingMass.kernel x n))
    EscapingMass.small_out.
Proof.
  intro Hobs.
  have Hnumeric := free_omega_observes_upper Hobs
    (f := fun _ : unit => (1 : R)) unit_test_bounded.
  rewrite upper_escaped_row_mass enum_real_expect_one
    EscapingMass.small_mass_half ?fmorph_div ?rmorphD ?rmorph1 ?ratr_nat in Hnumeric.
  apply (upper_separates_big_small (R := R)).
  rewrite upper_big_mass upper_small_mass. exact Hnumeric.
Qed.
End ObservationModelRegression.
