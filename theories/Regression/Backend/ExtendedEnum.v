(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals archimedean.
From mathcomp.classical Require Import classical_sets set_interval.
From mathcomp.analysis Require Import ereal sequences.
From PTree.Prob.Backend Require Import RatSubTypes DiscreteMC.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.Backend Require Import TwoLevelMeasureEnum.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Prob.Backend.FreeOmega Require Import FreeOmegaUpperExpectationEnum FreeOmegaUpperCouplingEnum FreeOmegaUpperContinuityEnum FreeOmegaUpperObservationEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Enum RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Section ExtendedEnumRegression.
Variable R : realType.

Example extended_enum_keeps_weight_two :
  @enum_extended_expect R unit (fun _ => 1) [:: (2%R, tt)] = 2%:E.
Proof. cbn [enum_extended_expect]. by rewrite /= rmorphD rmorph1 mule1 adde0. Qed.

Example extended_enum_zero_times_infinity :
  @enum_extended_expect R unit (fun _ => +oo) [:: (0%R, tt)] = 0.
Proof. cbn [enum_extended_expect]. by rewrite /= rmorph0 mul0e add0e. Qed.

(** This is increasing even in the RAW approximation order, not just
    numerically.  Each iteration adds one returned unit of weight while
    retaining the previous term.  No common finite mass bound exists. *)
Fixpoint growing_weight (n : nat) : FreeOmega Enum unit :=
  match n with
  | O => FOZero
  | S m => FOSample [:: (1%R, true); (1%R, false)]
      (fun b => if b then FORet tt else growing_weight m)
  end.

Lemma growing_weight_increasing n :
  free_omega_approx eq (growing_weight n) (growing_weight (S n)).
Proof.
  induction n as [|n IH]; cbn [growing_weight].
  - apply FOApproxZero.
  - eapply FOApproxSample with (S := eq).
    + apply sem_lift_refl. intro b. reflexivity.
    + intros x y ->. destruct y; [apply FOApproxRet; reflexivity|exact IH].
Qed.

Lemma growing_weight_value n :
  @free_omega_extended_upper R unit (growing_weight n) (fun _ => 1) = (n%:R)%:E.
Proof.
  induction n as [|n IH]; cbn [growing_weight free_omega_extended_upper enum_extended_expect].
  - reflexivity.
  - rewrite /= rmorph1 !mul1e adde0 IH -EFinD.
    congr (_%:E). by rewrite addrC natr1.
Qed.

Example growing_weight_has_infinite_upper :
  @free_omega_extended_upper R unit (FOLub growing_weight) (fun _ => 1) = +oo.
Proof.
  cbn [free_omega_extended_upper].
  rewrite (_ : (fun n => free_omega_extended_upper (growing_weight n) (fun _ => 1)) =
      (fun n => (n%:R : R)%:E));
    last by apply functional_extensionality=> n; apply growing_weight_value.
  exact: extended_upper_naturals.
Qed.

Theorem growing_weight_no_finite_observation (out : Enum unit) :
  ~ @free_omega_observes Enum Enum_SemanticMeasure Enum_SemanticOmega unit unit
      (fun x => x) (FOLub growing_weight) out.
Proof.
  intro Hobs.
  have Hvalue := @free_omega_observes_extended_real R unit unit
    (fun x => x) (FOLub growing_weight) out Hobs (fun _ => 1%R)
    (fun _ => ler01).
  rewrite growing_weight_has_infinite_upper in Hvalue. discriminate Hvalue.
Qed.

(** Monotone test continuity still holds through a weight-two node,
    including at an infinite limit.  No SubEnum bound can justify it. *)
Example weight_two_preserves_monotone_limit (f : nat -> unit -> \bar R) :
  (forall n x, 0 <= f n x) ->
  (forall x, nondecreasing_seq (fun n => f n x)) ->
  @enum_extended_expect R unit (fun x => extended_upper (fun n => f n x))
    [:: (2%R, tt)] =
  extended_upper (fun n => enum_extended_expect (f n) [:: (2%R, tt)]).
Proof. intros Hf Hi. exact (@enum_extended_expect_countable R unit [:: (2%R, tt)] f Hf Hi). Qed.

Example zero_weight_needs_no_monotonicity (f : nat -> unit -> \bar R) :
  (forall n x, 0 <= f n x) ->
  @enum_extended_expect R unit (fun x => extended_upper (fun n => f n x))
    [:: (0%R, tt)] =
  extended_upper (fun n => enum_extended_expect (f n) [:: (0%R, tt)]).
Proof.
  intro Hf. apply enum_extended_expect_countable_ae; [exact Hf|].
  intros p x [Heq|[]] Hnz. inversion Heq; subst p x.
  exfalso. apply Hnz. apply val_inj. reflexivity.
Qed.
End ExtendedEnumRegression.
