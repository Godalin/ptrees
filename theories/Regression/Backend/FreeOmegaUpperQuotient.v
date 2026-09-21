(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Backend Require Import TwoLevelMeasureSubEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Prob.Backend.FreeOmega Require Import FreeOmegaUpperExpectationSubEnum FreeOmegaUpperRelationalSubEnum FreeOmegaUpperQuotientSubEnum.
From PTree.Regression.Backend Require Import SubEnumRegression FreeOmegaEscapingMass FreeOmegaUpperExpectation FreeOmegaUpperObservation.
From PTree.Examples Require Import RandomWalk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section QuotientModelRegression.
Variable R : realType.
Local Notation upper := (free_omega_upper (R := R)).

(** Same support does not hide missing mass, even under a universal
    result relation and arbitrary combinations of quotient rules. *)
Theorem quotient_big_small_separated (T : unit -> unit -> Prop) :
  ~ @free_omega_qlift SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    unit unit T EscapingMass.big EscapingMass.small.
Proof.
  intro H. apply (upper_separates_big_small (R := R)).
  exact (free_omega_qlift_upper_mass R H).
Qed.

Theorem quotient_escaped_row_separated n :
  ~ @free_omega_qlift SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    unit unit eq (FOLub (fun x => EscapingMass.kernel x n)) EscapingMass.small.
Proof.
  intro H. have Hmass := free_omega_qlift_upper_mass R H.
  apply (upper_separates_big_small (R := R)).
  rewrite upper_escaped_row_mass in Hmass. by rewrite upper_big_mass.
Qed.

(** Equal total mass is not enough either: a non-increasing formal Lub
    cannot become a fair distribution by quotient reasoning. *)
Theorem quotient_raw_choice_not_fair :
  ~ @free_omega_qlift SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    bool bool eq raw_choice (FOSample subenum_fair (fun b => FORet b)).
Proof.
  intro H.
  have Hf : bounded_test (fun b : bool => if b then (1 : R) else 0).
  { intros []; split; try exact: ler01; exact: lexx. }
  have Heq := free_omega_qlift_eq_upper H Hf.
  have Hleft : upper raw_choice (fun b : bool => if b then 1 else 0) = 1.
  { apply (@upper_raw_choice_test R (fun b : bool => if b then 1 else 0) true);
      [exact Hf|reflexivity]. }
  change (upper raw_choice (fun b : bool => if b then 1 else 0) =
    upper EscapingMass.small (fun _ => 1)) in Heq.
  apply (upper_separates_big_small (R := R)).
  rewrite Hleft in Heq. rewrite upper_big_mass. exact Heq.
Qed.

(** Real unbounded behavior with a high-universe result carrier remains
    covered after quotient rewrites; no finite-support limit is assumed. *)
Theorem rewritten_random_walk_upper_mass x y mu :
  @free_omega_qlift SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega
    _ _ eq mu (walk_limit x y) -> upper mu (fun _ => 1) = 1.
Proof.
  intro H. rewrite (free_omega_qlift_upper_mass R H).
  apply random_walk_limit_upper_mass.
Qed.
End QuotientModelRegression.
